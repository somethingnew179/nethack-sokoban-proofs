import NetHack.Soko22Hazard87.AndIntroBlocks0084
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro21250 (p : Pattern) (ha : d8479 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8314 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8315 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8315, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8476 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8477 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8478 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8479 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21251 (p : Pattern) (ha : d94268 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8441 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21247 q ha hb
    | true =>
      simp only [d8441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21245 q ha hb
  have h2 (q : Pattern) (ha : d8442 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8443 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8444 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8448 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21248 q ha hb
    | true =>
      simp only [d8448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21246 q ha hb
  have h6 (q : Pattern) (ha : d8449 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8450 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8464 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21249 q ha hb
    | true =>
      simp only [d8464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21243 q ha hb
  have h9 (q : Pattern) (ha : d94264 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8480 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21250 q ha hb
    | true =>
      simp only [d8480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8481 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94265 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94266 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94267 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94268 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro21252 (p : Pattern) (ha : d610 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d482 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d483, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d488 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d489 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d513 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d610 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro21253 (p : Pattern) (ha : d616 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d482 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d483, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d488 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d522 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d523 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d616 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro21254 (p : Pattern) (ha : d8486 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8314 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8315 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8315, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d482 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d483 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d483, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8417 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8418 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8439 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8486 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro21255 (p : Pattern) (ha : d8491 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8314 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8315 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8315, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d482 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d483 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d483, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8417 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8445 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8446 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8491 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro21256 (p : Pattern) (ha : d8495 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8454 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8455 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8455, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8455, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6800 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6801 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d8456 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8457 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8458 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d8495 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21257 (p : Pattern) (ha : d8496 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6800 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6801 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d482 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d8460 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8461 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8462 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d8496 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21258 (p : Pattern) (ha : d8501 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8314 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8476 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8477 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8478 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d8501 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro21259 (p : Pattern) (ha : d94273 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8441 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21247 q ha hb
    | true =>
      simp only [d8441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21245 q ha hb
  have h2 (q : Pattern) (ha : d8442 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8443 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8444 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8448 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21248 q ha hb
    | true =>
      simp only [d8448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21246 q ha hb
  have h6 (q : Pattern) (ha : d8449 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8450 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8464 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21249 q ha hb
    | true =>
      simp only [d8464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21243 q ha hb
  have h9 (q : Pattern) (ha : d94264 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8480 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21250 q ha hb
    | true =>
      simp only [d8480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8481 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94265 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94266 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94267 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8487 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21254 q ha hb
    | true =>
      simp only [d8487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21252 q ha hb
  have h16 (q : Pattern) (ha : d8488 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8489 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d8489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d8490 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8492 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21255 q ha hb
    | true =>
      simp only [d8492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21253 q ha hb
  have h20 (q : Pattern) (ha : d8493 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d8494 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d8494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8497 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21256 q ha hb
    | true =>
      simp only [d8497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21257 q ha hb
  have h23 (q : Pattern) (ha : d94269 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d8502 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21258 q ha hb
    | true =>
      simp only [d8502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8503 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94270 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94271 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94272 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94273 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro21260 (p : Pattern) (ha : d94280 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8497 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21256 q ha hb
    | true =>
      simp only [d8497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21257 q ha hb
  have h2 (q : Pattern) (ha : d94269 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8502 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21258 q ha hb
    | true =>
      simp only [d8502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8503 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94270 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94278 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94279 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94280 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21261 (p : Pattern) (ha : d8535 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8530 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8531 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8531, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8531, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6846 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6847 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6847, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6847, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d8532 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8533 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8534 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d8535 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21262 (p : Pattern) (ha : d8539 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6846 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6847 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6847, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6847, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d684 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d8536 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8537 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8538 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d8539 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21263 (p : Pattern) (ha : d8555 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8378 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8379 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8379, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8379, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8552 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8553 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8554 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d8555 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro21264 (p : Pattern) (ha : d94290 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8540 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21261 q ha hb
    | true =>
      simp only [d8540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21262 q ha hb
  have h2 (q : Pattern) (ha : d94286 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8556 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21263 q ha hb
    | true =>
      simp only [d8556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8557 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94287 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94288 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94289 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94290 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21265 (p : Pattern) (ha : d94296 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8427 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21240 q ha hb
  have h2 (q : Pattern) (ha : d8428 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8436 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21240 q ha hb
    | true =>
      simp only [d8436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21242 q ha hb
  have h4 (q : Pattern) (ha : d8437 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8438 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94274 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21251 q ha hb
    | true =>
      simp only [d94274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21259 q ha hb
  have h7 (q : Pattern) (ha : d8515 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21244 q ha hb
    | true =>
      simp only [d8515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21235 q ha hb
  have h8 (q : Pattern) (ha : d94275 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94276 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94277 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94281 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21260 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21236 q ha hb
  have h13 (q : Pattern) (ha : d94282 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94283 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94284 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94285 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94291 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21264 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21238 q ha hb
  have h19 (q : Pattern) (ha : d94292 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d94293 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94294 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94295 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94296 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro21266 (p : Pattern) (ha : d94302 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94297 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21265 q ha hb
  have h2 (q : Pattern) (ha : d94298 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94299 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94300 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94301 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94302 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21267 (p : Pattern) (ha : d783 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d774 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d780 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d781 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d782 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d783 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21268 (p : Pattern) (ha : d793 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d780 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d781 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d782 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d793 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro21269 (p : Pattern) (ha : d950 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21267 q ha hb
    | true =>
      simp only [d939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d945 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21268 q ha hb
    | true =>
      simp only [d945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d946 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d947 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d948 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d949 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d950 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21270 (p : Pattern) (ha : d959 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d945 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21268 q ha hb
    | true =>
      simp only [d945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d946 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21271 (p : Pattern) (ha : d1063 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1006 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1060 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1061 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1062 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d1063 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro21272 (p : Pattern) (ha : d1069 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21271 q ha hb
    | true =>
      simp only [d1064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21273 (p : Pattern) (ha : d8582 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8577 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8578 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8578, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d774 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d775 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8579 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8580 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8581 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8582 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21274 (p : Pattern) (ha : d8588 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8583 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21273 q ha hb
    | true =>
      simp only [d8583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21267 q ha hb
  have h2 (q : Pattern) (ha : d8584 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8585 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8586 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8587 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8588 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21275 (p : Pattern) (ha : d8591 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8577 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d774 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d8579 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8580 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8581 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d8591 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21276 (p : Pattern) (ha : d8597 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8583 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21273 q ha hb
    | true =>
      simp only [d8583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21267 q ha hb
  have h2 (q : Pattern) (ha : d8584 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8585 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8586 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8587 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8592 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21275 q ha hb
    | true =>
      simp only [d8592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21268 q ha hb
  have h7 (q : Pattern) (ha : d8593 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8594 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8595 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8596 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8597 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21277 (p : Pattern) (ha : d8625 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6878 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6879 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6879, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d774 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d775 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8622 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8623 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8624 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8625 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21278 (p : Pattern) (ha : d8676 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8671 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21277 q ha hb
    | true =>
      simp only [d8671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21267 q ha hb
  have h2 (q : Pattern) (ha : d8672 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8673 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8674 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8675 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21267 q ha hb
    | true =>
      simp only [d939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8676 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21279 (p : Pattern) (ha : d806 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d774 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d780 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d781 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d805 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d806 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21280 (p : Pattern) (ha : d816 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d774 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d780 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d814 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d815 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d816 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21281 (p : Pattern) (ha : d8602 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8577 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8578 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8578, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d774 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d775 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8579 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8580 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8601 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8602 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21282 (p : Pattern) (ha : d8609 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8577 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8578 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8578, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d774 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d775 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8579 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8607 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8608 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8609 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21283 (p : Pattern) (ha : d8621 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8616 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8617 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8617, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8617, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6878 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6879 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6879, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8618 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8619 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8620 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8621 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21284 (p : Pattern) (ha : d8641 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8577 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8578 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8578, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8638 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8639 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8640 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8641 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21285 (p : Pattern) (ha : d94308 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8603 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21281 q ha hb
    | true =>
      simp only [d8603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21279 q ha hb
  have h2 (q : Pattern) (ha : d8604 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8605 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8606 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8610 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21282 q ha hb
    | true =>
      simp only [d8610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21280 q ha hb
  have h6 (q : Pattern) (ha : d8611 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8612 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8626 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21283 q ha hb
    | true =>
      simp only [d8626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21277 q ha hb
  have h9 (q : Pattern) (ha : d94304 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8642 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21284 q ha hb
    | true =>
      simp only [d8642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8643 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94305 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94306 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94307 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94308 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro21286 (p : Pattern) (ha : d916 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d774 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d780 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d781 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d805 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d916 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro21287 (p : Pattern) (ha : d922 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d774 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d780 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d814 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d815 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d922 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro21288 (p : Pattern) (ha : d8648 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8577 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8578 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8578, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d774 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d775 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8579 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8580 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8601 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8648 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro21289 (p : Pattern) (ha : d8653 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8577 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8578 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8578, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d774 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d775 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8579 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8607 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8608 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8653 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro21290 (p : Pattern) (ha : d8657 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8616 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8617 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8617, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8617, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6878 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6879 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d8618 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8619 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8620 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d8657 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21291 (p : Pattern) (ha : d8658 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6878 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6879 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d774 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d8622 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8623 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8624 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d8658 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21292 (p : Pattern) (ha : d8663 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8577 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8638 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8639 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8640 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d8663 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro21293 (p : Pattern) (ha : d94313 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8603 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21281 q ha hb
    | true =>
      simp only [d8603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21279 q ha hb
  have h2 (q : Pattern) (ha : d8604 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8605 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8606 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8610 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21282 q ha hb
    | true =>
      simp only [d8610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21280 q ha hb
  have h6 (q : Pattern) (ha : d8611 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8612 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8626 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21283 q ha hb
    | true =>
      simp only [d8626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21277 q ha hb
  have h9 (q : Pattern) (ha : d94304 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8642 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21284 q ha hb
    | true =>
      simp only [d8642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8643 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94305 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94306 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94307 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8649 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21288 q ha hb
    | true =>
      simp only [d8649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21286 q ha hb
  have h16 (q : Pattern) (ha : d8650 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8651 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d8651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d8652 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8654 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21289 q ha hb
    | true =>
      simp only [d8654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21287 q ha hb
  have h20 (q : Pattern) (ha : d8655 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d8656 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d8656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8659 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21290 q ha hb
    | true =>
      simp only [d8659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21291 q ha hb
  have h23 (q : Pattern) (ha : d94309 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d8664 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21292 q ha hb
    | true =>
      simp only [d8664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8665 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94310 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94311 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94312 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94313 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro21294 (p : Pattern) (ha : d94320 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8659 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21290 q ha hb
    | true =>
      simp only [d8659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21291 q ha hb
  have h2 (q : Pattern) (ha : d94309 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8664 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21292 q ha hb
    | true =>
      simp only [d8664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8665 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94310 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94318 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94319 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94320 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21295 (p : Pattern) (ha : d8697 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8692 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8693 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8693, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8693, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6924 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6925 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6925, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6925, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d8694 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8695 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8696 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d8697 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21296 (p : Pattern) (ha : d8701 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6924 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6925 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6925, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6925, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1006 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d8698 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8699 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8700 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d8701 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21297 (p : Pattern) (ha : d8721 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8716 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8717 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8717, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8717, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8718 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8719 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8720 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d8721 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro21298 (p : Pattern) (ha : d94330 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8702 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21295 q ha hb
    | true =>
      simp only [d8702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21296 q ha hb
  have h2 (q : Pattern) (ha : d94326 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8722 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21297 q ha hb
    | true =>
      simp only [d8722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8723 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94327 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94328 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94329 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94330 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21299 (p : Pattern) (ha : d94336 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8589 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21274 q ha hb
  have h2 (q : Pattern) (ha : d8590 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8598 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21274 q ha hb
    | true =>
      simp only [d8598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21276 q ha hb
  have h4 (q : Pattern) (ha : d8599 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8600 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94314 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21285 q ha hb
    | true =>
      simp only [d94314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21293 q ha hb
  have h7 (q : Pattern) (ha : d8677 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21278 q ha hb
    | true =>
      simp only [d8677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21269 q ha hb
  have h8 (q : Pattern) (ha : d94315 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94316 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94317 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94321 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21294 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21270 q ha hb
  have h13 (q : Pattern) (ha : d94322 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94323 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94324 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94325 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94331 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21298 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21272 q ha hb
  have h19 (q : Pattern) (ha : d94332 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d94333 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94334 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94335 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94336 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro21300 (p : Pattern) (ha : d94342 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94337 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21299 q ha hb
  have h2 (q : Pattern) (ha : d94338 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94339 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94340 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94341 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94342 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21301 (p : Pattern) (ha : d1162 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1153 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1159 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1160 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1161 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1162 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21302 (p : Pattern) (ha : d1172 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1153 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1159 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1160 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1161 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d1172 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro21303 (p : Pattern) (ha : d1361 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1350 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21301 q ha hb
    | true =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1351 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1352 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1353 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1354 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1356 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21302 q ha hb
    | true =>
      simp only [d1356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1357 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1358 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1359 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1360 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1361 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21304 (p : Pattern) (ha : d1370 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1356 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21302 q ha hb
    | true =>
      simp only [d1356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1357 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1358 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1359 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1360 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1370 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21305 (p : Pattern) (ha : d1497 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1431 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1432 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1494 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1495 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1496 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d1497 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro21306 (p : Pattern) (ha : d1503 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1498 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21305 q ha hb
    | true =>
      simp only [d1498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1499 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1500 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1501 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1502 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1503 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21307 (p : Pattern) (ha : d8749 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8744 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8745 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8745, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1153 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1154 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8746 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8747 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8748 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8749 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21308 (p : Pattern) (ha : d8755 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8750 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21307 q ha hb
    | true =>
      simp only [d8750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21301 q ha hb
  have h2 (q : Pattern) (ha : d8751 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8752 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8753 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8754 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8755 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21309 (p : Pattern) (ha : d8758 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8744 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1153 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8747 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8748 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d8758 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21310 (p : Pattern) (ha : d8764 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8750 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21307 q ha hb
    | true =>
      simp only [d8750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21301 q ha hb
  have h2 (q : Pattern) (ha : d8751 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8752 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8753 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8754 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8759 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21309 q ha hb
    | true =>
      simp only [d8759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21302 q ha hb
  have h7 (q : Pattern) (ha : d8760 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8761 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8762 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8763 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8764 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21311 (p : Pattern) (ha : d8792 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6957 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6958 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6958, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1153 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1154 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8789 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8790 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8791 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8792 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21312 (p : Pattern) (ha : d8843 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8838 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21311 q ha hb
    | true =>
      simp only [d8838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21301 q ha hb
  have h2 (q : Pattern) (ha : d8839 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8840 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8841 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8842 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1350 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21301 q ha hb
    | true =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1351 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1352 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1353 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1354 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8843 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21313 (p : Pattern) (ha : d1185 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1153 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1159 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1160 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1184 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1185 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21314 (p : Pattern) (ha : d1195 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1153 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1159 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1193 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1194 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1195 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21315 (p : Pattern) (ha : d8769 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8744 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8745 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8745, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1153 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1154 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8746 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8747 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8768 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8769 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21316 (p : Pattern) (ha : d8776 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8744 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8745 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8745, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1153 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1154 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8746 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8774 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8775 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8776 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21317 (p : Pattern) (ha : d8788 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8783 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8784 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8784, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8784, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6957 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6958 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6958, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8785 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8786 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8787 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8788 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21318 (p : Pattern) (ha : d8808 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8744 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8745 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8745, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8805 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8806 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8807 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8808 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21319 (p : Pattern) (ha : d94349 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8770 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21315 q ha hb
    | true =>
      simp only [d8770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21313 q ha hb
  have h2 (q : Pattern) (ha : d8771 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8772 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8773 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8777 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21316 q ha hb
    | true =>
      simp only [d8777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21314 q ha hb
  have h6 (q : Pattern) (ha : d8778 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8779 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8793 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21317 q ha hb
    | true =>
      simp only [d8793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21311 q ha hb
  have h9 (q : Pattern) (ha : d94345 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8809 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21318 q ha hb
    | true =>
      simp only [d8809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8810 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94346 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94347 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94348 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94349 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro21320 (p : Pattern) (ha : d1327 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1153 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1159 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1160 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1184 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1327 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro21321 (p : Pattern) (ha : d1333 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1153 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1159 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1193 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1194 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1333 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro21322 (p : Pattern) (ha : d8815 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8744 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8745 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8745, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1153 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1154 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8746 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8747 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8768 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8815 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro21323 (p : Pattern) (ha : d8820 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8744 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8745 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8745, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1153 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1154 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8746 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8774 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8775 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8820 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro21324 (p : Pattern) (ha : d8824 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8783 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8784 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8784, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8784, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6957 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6958 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d8785 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8786 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8787 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d8824 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21325 (p : Pattern) (ha : d8825 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6957 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6958 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1153 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d8789 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8790 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8791 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d8825 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21326 (p : Pattern) (ha : d8830 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8744 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8805 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8806 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8807 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d8830 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro21327 (p : Pattern) (ha : d94354 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8770 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21315 q ha hb
    | true =>
      simp only [d8770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21313 q ha hb
  have h2 (q : Pattern) (ha : d8771 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8772 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8773 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8777 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21316 q ha hb
    | true =>
      simp only [d8777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21314 q ha hb
  have h6 (q : Pattern) (ha : d8778 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8779 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8793 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21317 q ha hb
    | true =>
      simp only [d8793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21311 q ha hb
  have h9 (q : Pattern) (ha : d94345 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8809 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21318 q ha hb
    | true =>
      simp only [d8809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8810 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94346 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94347 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94348 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8816 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21322 q ha hb
    | true =>
      simp only [d8816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21320 q ha hb
  have h16 (q : Pattern) (ha : d8817 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8818 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d8818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d8819 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8821 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21323 q ha hb
    | true =>
      simp only [d8821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21321 q ha hb
  have h20 (q : Pattern) (ha : d8822 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d8823 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d8823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8826 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21324 q ha hb
    | true =>
      simp only [d8826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21325 q ha hb
  have h23 (q : Pattern) (ha : d94350 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d8831 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21326 q ha hb
    | true =>
      simp only [d8831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8832 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94351 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94352 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94353 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94354 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro21328 (p : Pattern) (ha : d94361 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8826 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21324 q ha hb
    | true =>
      simp only [d8826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21325 q ha hb
  have h2 (q : Pattern) (ha : d94350 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8831 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21326 q ha hb
    | true =>
      simp only [d8831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8832 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94351 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94359 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94360 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94361 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21329 (p : Pattern) (ha : d8864 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8859 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8860 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8860, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8860, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7003 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7004 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7004, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7004, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d8861 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8862 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8863 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d8864 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21330 (p : Pattern) (ha : d8868 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7003 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7004 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7004, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7004, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1431 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d8865 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8866 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8867 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d8868 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21331 (p : Pattern) (ha : d8888 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8883 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8884 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8884, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8884, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8885 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8886 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8887 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d8888 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro21332 (p : Pattern) (ha : d94371 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8869 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21329 q ha hb
    | true =>
      simp only [d8869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21330 q ha hb
  have h2 (q : Pattern) (ha : d94367 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8889 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21331 q ha hb
    | true =>
      simp only [d8889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8890 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94368 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94369 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94370 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94371 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21333 (p : Pattern) (ha : d94377 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8756 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21308 q ha hb
  have h2 (q : Pattern) (ha : d8757 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8765 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21308 q ha hb
    | true =>
      simp only [d8765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21310 q ha hb
  have h4 (q : Pattern) (ha : d8766 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8767 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94355 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21319 q ha hb
    | true =>
      simp only [d94355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21327 q ha hb
  have h7 (q : Pattern) (ha : d8844 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21312 q ha hb
    | true =>
      simp only [d8844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21303 q ha hb
  have h8 (q : Pattern) (ha : d94356 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94357 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94358 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94362 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21328 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21304 q ha hb
  have h13 (q : Pattern) (ha : d94363 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94364 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94365 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94366 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94372 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21332 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21306 q ha hb
  have h19 (q : Pattern) (ha : d94373 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d94374 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94375 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94376 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94377 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro21334 (p : Pattern) (ha : d94383 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94378 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21333 q ha hb
  have h2 (q : Pattern) (ha : d94379 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94380 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94381 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94382 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94383 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21335 (p : Pattern) (ha : d1623 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1614 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1620 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1621 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1622 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1623 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21336 (p : Pattern) (ha : d1633 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1614 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1620 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1621 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1622 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d1633 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro21337 (p : Pattern) (ha : d1838 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1827 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21335 q ha hb
    | true =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1828 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1829 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1830 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1831 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1833 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21336 q ha hb
    | true =>
      simp only [d1833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1834 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1835 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1836 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1837 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1838 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21338 (p : Pattern) (ha : d1847 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1833 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21336 q ha hb
    | true =>
      simp only [d1833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1834 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1835 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1836 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1837 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1847 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21339 (p : Pattern) (ha : d1974 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1908 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1909 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1971 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1972 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1973 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d1974 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro21340 (p : Pattern) (ha : d1980 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1975 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21339 q ha hb
    | true =>
      simp only [d1975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1976 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1977 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1978 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1979 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1980 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21341 (p : Pattern) (ha : d8917 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8912 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8913 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8913, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1614 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1615 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8914 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8915 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8916 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8917 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21342 (p : Pattern) (ha : d8923 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8918 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21341 q ha hb
    | true =>
      simp only [d8918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21335 q ha hb
  have h2 (q : Pattern) (ha : d8919 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8920 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8921 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8922 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8923 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21343 (p : Pattern) (ha : d8926 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8912 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1614 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8915 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8916 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d8926 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21344 (p : Pattern) (ha : d8932 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8918 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21341 q ha hb
    | true =>
      simp only [d8918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21335 q ha hb
  have h2 (q : Pattern) (ha : d8919 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8920 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8921 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8922 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8927 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21343 q ha hb
    | true =>
      simp only [d8927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21336 q ha hb
  have h7 (q : Pattern) (ha : d8928 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8929 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8930 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8931 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8932 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21345 (p : Pattern) (ha : d8960 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7037 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7038 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7038, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1614 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1615 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8957 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8958 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8959 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8960 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21346 (p : Pattern) (ha : d9011 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9006 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21345 q ha hb
    | true =>
      simp only [d9006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21335 q ha hb
  have h2 (q : Pattern) (ha : d9007 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9008 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9009 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9010 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1827 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21335 q ha hb
    | true =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1828 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1829 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1830 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1831 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9011 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21347 (p : Pattern) (ha : d1646 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1614 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1620 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1621 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1645 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1646 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21348 (p : Pattern) (ha : d1656 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1614 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1620 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1654 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1655 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1656 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21349 (p : Pattern) (ha : d8937 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8912 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8913 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8913, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1614 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1615 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8914 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8915 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8936 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8937 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21350 (p : Pattern) (ha : d8944 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8912 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8913 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8913, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1614 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1615 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8914 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8942 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8943 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8944 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21351 (p : Pattern) (ha : d8956 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8951 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8952 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8952, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8952, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7037 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7038 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7038, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8953 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8954 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8955 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8956 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21352 (p : Pattern) (ha : d8976 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8912 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8913 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8913, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8973 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8974 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8975 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8976 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21353 (p : Pattern) (ha : d94391 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8938 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21349 q ha hb
    | true =>
      simp only [d8938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21347 q ha hb
  have h2 (q : Pattern) (ha : d8939 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8940 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8941 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8945 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21350 q ha hb
    | true =>
      simp only [d8945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21348 q ha hb
  have h6 (q : Pattern) (ha : d8946 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8947 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8961 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21351 q ha hb
    | true =>
      simp only [d8961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21345 q ha hb
  have h9 (q : Pattern) (ha : d94387 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8977 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21352 q ha hb
    | true =>
      simp only [d8977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8978 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94388 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94389 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94390 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94391 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro21354 (p : Pattern) (ha : d1804 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1614 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1620 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1621 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1645 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1804 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro21355 (p : Pattern) (ha : d1810 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1614 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1620 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1654 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1655 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1810 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro21356 (p : Pattern) (ha : d8983 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8912 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8913 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8913, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1614 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1615 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8914 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8915 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8936 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8983 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro21357 (p : Pattern) (ha : d8988 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8912 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8913 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8913, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1614 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1615 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d8914 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8942 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8943 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8988 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro21358 (p : Pattern) (ha : d8992 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8951 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8952 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8952, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8952, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7037 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7038 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d8953 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8954 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8955 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d8992 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21359 (p : Pattern) (ha : d8993 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7037 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7038 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1614 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d8957 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8958 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8959 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d8993 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21360 (p : Pattern) (ha : d8998 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8912 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8973 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8974 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8975 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d8998 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro21361 (p : Pattern) (ha : d94396 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8938 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21349 q ha hb
    | true =>
      simp only [d8938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21347 q ha hb
  have h2 (q : Pattern) (ha : d8939 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8940 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8941 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8945 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21350 q ha hb
    | true =>
      simp only [d8945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21348 q ha hb
  have h6 (q : Pattern) (ha : d8946 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8947 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8961 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21351 q ha hb
    | true =>
      simp only [d8961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21345 q ha hb
  have h9 (q : Pattern) (ha : d94387 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8977 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21352 q ha hb
    | true =>
      simp only [d8977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8978 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94388 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94389 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94390 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8984 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21356 q ha hb
    | true =>
      simp only [d8984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21354 q ha hb
  have h16 (q : Pattern) (ha : d8985 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8986 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d8986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d8987 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8989 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21357 q ha hb
    | true =>
      simp only [d8989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21355 q ha hb
  have h20 (q : Pattern) (ha : d8990 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d8991 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d8991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8994 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21358 q ha hb
    | true =>
      simp only [d8994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21359 q ha hb
  have h23 (q : Pattern) (ha : d94392 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d8999 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21360 q ha hb
    | true =>
      simp only [d8999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d9000 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d9000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94393 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94394 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94395 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94396 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro21362 (p : Pattern) (ha : d94403 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8994 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21358 q ha hb
    | true =>
      simp only [d8994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21359 q ha hb
  have h2 (q : Pattern) (ha : d94392 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8999 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21360 q ha hb
    | true =>
      simp only [d8999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9000 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94393 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94401 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94402 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94403 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21363 (p : Pattern) (ha : d9032 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9027 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9028 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9028, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9028, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7083 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7084 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7084, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7084, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d9029 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9030 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9031 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d9032 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21364 (p : Pattern) (ha : d9036 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7083 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7084 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7084, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7084, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d9033 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9034 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9035 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d9036 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21365 (p : Pattern) (ha : d9056 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9052 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9052, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9052, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9053 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9054 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d9055 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d9056 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro21366 (p : Pattern) (ha : d94413 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9037 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21363 q ha hb
    | true =>
      simp only [d9037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21364 q ha hb
  have h2 (q : Pattern) (ha : d94409 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9057 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21365 q ha hb
    | true =>
      simp only [d9057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9058 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94410 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94411 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94412 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94413 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21367 (p : Pattern) (ha : d94419 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8924 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21342 q ha hb
  have h2 (q : Pattern) (ha : d8925 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8933 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21342 q ha hb
    | true =>
      simp only [d8933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21344 q ha hb
  have h4 (q : Pattern) (ha : d8934 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8935 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94397 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21353 q ha hb
    | true =>
      simp only [d94397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21361 q ha hb
  have h7 (q : Pattern) (ha : d9012 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21346 q ha hb
    | true =>
      simp only [d9012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21337 q ha hb
  have h8 (q : Pattern) (ha : d94398 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94399 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94400 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94404 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21362 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21338 q ha hb
  have h13 (q : Pattern) (ha : d94405 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94406 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94407 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94408 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94414 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21366 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21340 q ha hb
  have h19 (q : Pattern) (ha : d94415 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d94416 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94417 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94418 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94419 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro21368 (p : Pattern) (ha : d94425 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94420 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21367 q ha hb
  have h2 (q : Pattern) (ha : d94421 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94422 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94423 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94424 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94425 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21369 (p : Pattern) (ha : d2106 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2097 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2103 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2104 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2105 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2106 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21370 (p : Pattern) (ha : d2116 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2097 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2103 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2104 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d2105 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d2116 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro21371 (p : Pattern) (ha : d2316 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2305 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21369 q ha hb
    | true =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2306 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2307 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2308 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2309 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2311 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21370 q ha hb
    | true =>
      simp only [d2311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2312 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2313 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2314 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2315 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2316 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21372 (p : Pattern) (ha : d2325 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2311 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21370 q ha hb
    | true =>
      simp only [d2311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2312 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2313 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2314 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2315 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2325 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21373 (p : Pattern) (ha : d2452 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2386 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2387 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2449 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2450 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d2451 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d2452 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro21374 (p : Pattern) (ha : d2458 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2453 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21373 q ha hb
    | true =>
      simp only [d2453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2454 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2455 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2456 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2457 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2458 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21375 (p : Pattern) (ha : d9086 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9081 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9082 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9082, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2097 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2098 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d9083 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9084 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9085 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9086 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21376 (p : Pattern) (ha : d9092 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9087 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21375 q ha hb
    | true =>
      simp only [d9087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21369 q ha hb
  have h2 (q : Pattern) (ha : d9088 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9089 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9090 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9091 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9092 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21377 (p : Pattern) (ha : d9095 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9081 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2097 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d9083 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9084 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9085 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d9095 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21378 (p : Pattern) (ha : d9101 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9087 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21375 q ha hb
    | true =>
      simp only [d9087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21369 q ha hb
  have h2 (q : Pattern) (ha : d9088 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9089 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9090 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9091 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9096 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21377 q ha hb
    | true =>
      simp only [d9096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21370 q ha hb
  have h7 (q : Pattern) (ha : d9097 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9098 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9099 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9100 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9101 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21379 (p : Pattern) (ha : d9129 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7118 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7119 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7119, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2097 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2098 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d9126 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9127 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9128 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9129 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21380 (p : Pattern) (ha : d9180 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9175 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21379 q ha hb
    | true =>
      simp only [d9175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21369 q ha hb
  have h2 (q : Pattern) (ha : d9176 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9177 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9178 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9179 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2305 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21369 q ha hb
    | true =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2306 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2307 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2308 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2309 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9180 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21381 (p : Pattern) (ha : d2129 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2097 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2103 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2104 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2128 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2129 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21382 (p : Pattern) (ha : d2139 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2097 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2103 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2137 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2138 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2139 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21383 (p : Pattern) (ha : d9106 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9081 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9082 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9082, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2097 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2098 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d9083 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9084 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9105 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9106 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21384 (p : Pattern) (ha : d9113 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9081 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9082 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9082, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2097 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2098 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d9083 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9111 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9112 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9113 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21385 (p : Pattern) (ha : d9125 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9120 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9121 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9121, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9121, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7118 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7119 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7119, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d9122 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9123 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9124 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9125 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21386 (p : Pattern) (ha : d9145 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9081 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9082 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9082, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9142 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9143 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9144 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9145 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21387 (p : Pattern) (ha : d94434 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9107 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21383 q ha hb
    | true =>
      simp only [d9107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21381 q ha hb
  have h2 (q : Pattern) (ha : d9108 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9109 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9110 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9114 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21384 q ha hb
    | true =>
      simp only [d9114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21382 q ha hb
  have h6 (q : Pattern) (ha : d9115 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9116 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9130 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21385 q ha hb
    | true =>
      simp only [d9130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21379 q ha hb
  have h9 (q : Pattern) (ha : d94430 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9146 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21386 q ha hb
    | true =>
      simp only [d9146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9147 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94431 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94432 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94433 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94434 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro21388 (p : Pattern) (ha : d2282 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2097 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2103 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2104 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2128 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2282 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro21389 (p : Pattern) (ha : d2288 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2097 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2103 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2137 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2138 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2288 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro21390 (p : Pattern) (ha : d9152 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9081 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9082 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9082, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2097 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2098 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d9083 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9084 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9105 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9152 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro21391 (p : Pattern) (ha : d9157 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9081 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9082 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9082, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2097 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2098 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d9083 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9111 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9112 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9157 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro21392 (p : Pattern) (ha : d9161 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9121 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9121, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9121, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7118 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7119 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d9122 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9123 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9124 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d9161 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21393 (p : Pattern) (ha : d9162 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7118 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7119 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2097 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d9126 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9127 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9128 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d9162 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21394 (p : Pattern) (ha : d9167 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9081 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9142 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9143 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d9144 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d9167 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro21395 (p : Pattern) (ha : d94439 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9107 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21383 q ha hb
    | true =>
      simp only [d9107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21381 q ha hb
  have h2 (q : Pattern) (ha : d9108 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9109 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9110 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9114 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21384 q ha hb
    | true =>
      simp only [d9114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21382 q ha hb
  have h6 (q : Pattern) (ha : d9115 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9116 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9130 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21385 q ha hb
    | true =>
      simp only [d9130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21379 q ha hb
  have h9 (q : Pattern) (ha : d94430 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9146 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21386 q ha hb
    | true =>
      simp only [d9146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9147 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94431 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94432 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94433 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9153 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21390 q ha hb
    | true =>
      simp only [d9153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21388 q ha hb
  have h16 (q : Pattern) (ha : d9154 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9155 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9156 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9158 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21391 q ha hb
    | true =>
      simp only [d9158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21389 q ha hb
  have h20 (q : Pattern) (ha : d9159 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9160 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d9163 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21392 q ha hb
    | true =>
      simp only [d9163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21393 q ha hb
  have h23 (q : Pattern) (ha : d94435 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d9168 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21394 q ha hb
    | true =>
      simp only [d9168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d9169 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d9169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94436 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94437 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94438 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94439 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro21396 (p : Pattern) (ha : d94446 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9163 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21392 q ha hb
    | true =>
      simp only [d9163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21393 q ha hb
  have h2 (q : Pattern) (ha : d94435 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9168 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21394 q ha hb
    | true =>
      simp only [d9168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9169 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94436 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94444 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94445 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94446 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21397 (p : Pattern) (ha : d9201 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9196 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9197 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9197, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9197, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7164 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7165 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7165, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7165, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d9198 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9199 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9200 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d9201 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21398 (p : Pattern) (ha : d9205 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7164 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7165 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7165, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7165, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2386 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d9202 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9203 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9204 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d9205 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21399 (p : Pattern) (ha : d9225 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9220 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9221 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9221, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9221, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9222 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9223 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d9224 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d9225 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro21400 (p : Pattern) (ha : d94456 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9206 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21397 q ha hb
    | true =>
      simp only [d9206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21398 q ha hb
  have h2 (q : Pattern) (ha : d94452 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9226 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21399 q ha hb
    | true =>
      simp only [d9226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9227 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94453 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94454 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94455 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94456 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21401 (p : Pattern) (ha : d94462 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9093 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21376 q ha hb
  have h2 (q : Pattern) (ha : d9094 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9102 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21376 q ha hb
    | true =>
      simp only [d9102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21378 q ha hb
  have h4 (q : Pattern) (ha : d9103 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9104 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d9104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94440 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21387 q ha hb
    | true =>
      simp only [d94440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21395 q ha hb
  have h7 (q : Pattern) (ha : d9181 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21380 q ha hb
    | true =>
      simp only [d9181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21371 q ha hb
  have h8 (q : Pattern) (ha : d94441 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94442 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94443 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94447 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21396 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21372 q ha hb
  have h13 (q : Pattern) (ha : d94448 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94449 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94450 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94451 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94457 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21400 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21374 q ha hb
  have h19 (q : Pattern) (ha : d94458 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d94459 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94460 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94461 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94462 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro21402 (p : Pattern) (ha : d94468 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94463 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21401 q ha hb
  have h2 (q : Pattern) (ha : d94464 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94465 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94466 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94467 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94468 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21403 (p : Pattern) (ha : d94474 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d94303 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21232 q ha hb
    | true =>
      simp only [d94303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21266 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d94343 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21300 q ha hb
  have h3 (q : Pattern) (ha : d94344 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94384 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21334 q ha hb
  have h5 (q : Pattern) (ha : d94385 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94386 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94426 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21368 q ha hb
  have h8 (q : Pattern) (ha : d94427 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94428 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94429 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94469 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21402 q ha hb
  have h12 (q : Pattern) (ha : d94470 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94471 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94472 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94473 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d94473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94474 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d94474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro21404 (p : Pattern) (ha : d94480 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94475 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d94475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21403 q ha hb
    | true =>
      simp only [d94475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94476 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d94476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94477 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d94477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94478 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d94478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94479 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d94479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94480 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d94480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21405 (p : Pattern) (ha : d94486 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94481 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d94481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21404 q ha hb
    | true =>
      simp only [d94481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94482 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d94482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94483 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d94483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94484 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d94484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94485 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d94485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94486 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d94486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21406 (p : Pattern) (ha : d94492 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94487 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d94487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21405 q ha hb
    | true =>
      simp only [d94487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94488 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d94488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94489 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d94489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94490 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d94490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94491 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d94491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94492 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d94492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21407 (p : Pattern) (ha : d94498 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94493 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d94493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21406 q ha hb
    | true =>
      simp only [d94493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94494 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d94494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94495 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d94495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94496 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d94496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94497 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d94497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94498 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d94498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21408 (p : Pattern) (ha : d94504 p = 1) (hb : d100902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94499 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d94499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21407 q ha hb
    | true =>
      simp only [d94499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94500 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d94500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d94501 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d94501, d100902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94501, d100902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d94502 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d94502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94503 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d94503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d94504 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d94504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro21409 (p : Pattern) (ha : d94510 p = 1) (hb : d100902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94505 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d94505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21408 q ha hb
    | true =>
      simp only [d94505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94506 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d94506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94507 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d94507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94508 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d94508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94509 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d94509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94510 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d94510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21410 (p : Pattern) (ha : d94516 p = 1) (hb : d100902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94511 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d94511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21409 q ha hb
    | true =>
      simp only [d94511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94512 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d94512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94513 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d94513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94514 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d94514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94515 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d94515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94516 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d94516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21411 (p : Pattern) (ha : d53647 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21197 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21198 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21212 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21213 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
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
theorem andIntro21412 (p : Pattern) (ha : d94521 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8246 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21206 q ha hb
    | true =>
      simp only [d8246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21191 q ha hb
  have h2 (q : Pattern) (ha : d8292 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8293 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8294 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8295 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94521 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21413 (p : Pattern) (ha : d94531 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8268 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21209 q ha hb
    | true =>
      simp only [d8268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21194 q ha hb
  have h2 (q : Pattern) (ha : d94527 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94528 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94529 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94530 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94531 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21414 (p : Pattern) (ha : d94537 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8297 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21214 q ha hb
    | true =>
      simp only [d8297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21215 q ha hb
  have h2 (q : Pattern) (ha : d8298 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94519 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94520 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94522 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21412 q ha hb
  have h6 (q : Pattern) (ha : d94523 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94524 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94525 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94526 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94532 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21413 q ha hb
  have h11 (q : Pattern) (ha : d94533 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94534 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94535 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94536 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94537 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro21415 (p : Pattern) (ha : d94543 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21411 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94538 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21414 q ha hb
  have h7 (q : Pattern) (ha : d94539 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94540 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94541 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94542 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94543 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21416 (p : Pattern) (ha : d94546 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8430 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21241 q ha hb
    | true =>
      simp only [d8430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21234 q ha hb
  have h2 (q : Pattern) (ha : d8431 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8432 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8433 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8434 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94546 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21417 (p : Pattern) (ha : d94555 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8378 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8379 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8379, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8379, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d684 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d94552 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94553 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94554 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d94555 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21418 (p : Pattern) (ha : d94561 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94556 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21417 q ha hb
    | true =>
      simp only [d94556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21237 q ha hb
  have h2 (q : Pattern) (ha : d94557 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94558 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94559 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94560 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94561 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21419 (p : Pattern) (ha : d94567 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8436 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21240 q ha hb
    | true =>
      simp only [d8436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21242 q ha hb
  have h2 (q : Pattern) (ha : d8437 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94544 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94545 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94547 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21416 q ha hb
  have h6 (q : Pattern) (ha : d94548 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94549 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94550 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94551 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94562 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21418 q ha hb
  have h11 (q : Pattern) (ha : d94563 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94564 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94565 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94566 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94567 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro21420 (p : Pattern) (ha : d94573 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94568 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21419 q ha hb
  have h2 (q : Pattern) (ha : d94569 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94570 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94571 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94572 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94573 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21421 (p : Pattern) (ha : d94577 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8592 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21275 q ha hb
    | true =>
      simp only [d8592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21268 q ha hb
  have h2 (q : Pattern) (ha : d8593 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8594 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8595 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8596 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94577 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21422 (p : Pattern) (ha : d94586 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8716 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8717 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8717, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8717, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1006 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d94583 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94584 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94585 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d94586 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21423 (p : Pattern) (ha : d94592 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94587 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21422 q ha hb
    | true =>
      simp only [d94587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21271 q ha hb
  have h2 (q : Pattern) (ha : d94588 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94589 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94590 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94591 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94592 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21424 (p : Pattern) (ha : d94598 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8598 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21274 q ha hb
    | true =>
      simp only [d8598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21276 q ha hb
  have h2 (q : Pattern) (ha : d8599 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94575 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94576 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94578 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21421 q ha hb
  have h6 (q : Pattern) (ha : d94579 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94580 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94581 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94582 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94593 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21423 q ha hb
  have h11 (q : Pattern) (ha : d94594 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94595 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94596 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94597 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94598 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro21425 (p : Pattern) (ha : d94604 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94599 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21424 q ha hb
  have h2 (q : Pattern) (ha : d94600 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94601 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94602 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94603 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94604 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21426 (p : Pattern) (ha : d94609 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8759 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21309 q ha hb
    | true =>
      simp only [d8759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21302 q ha hb
  have h2 (q : Pattern) (ha : d8760 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8761 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8762 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8763 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94609 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21427 (p : Pattern) (ha : d94618 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8883 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8884 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8884, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8884, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1431 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d94615 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94616 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94617 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d94618 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21428 (p : Pattern) (ha : d94624 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94619 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21427 q ha hb
    | true =>
      simp only [d94619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21305 q ha hb
  have h2 (q : Pattern) (ha : d94620 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94621 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94622 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94623 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94624 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21429 (p : Pattern) (ha : d94630 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8765 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21308 q ha hb
    | true =>
      simp only [d8765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21310 q ha hb
  have h2 (q : Pattern) (ha : d8766 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94607 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94608 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94610 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21426 q ha hb
  have h6 (q : Pattern) (ha : d94611 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94612 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94613 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94614 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94625 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21428 q ha hb
  have h11 (q : Pattern) (ha : d94626 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94627 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94628 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94629 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94630 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro21430 (p : Pattern) (ha : d94636 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94631 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21429 q ha hb
  have h2 (q : Pattern) (ha : d94632 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94633 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94634 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94635 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94636 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21431 (p : Pattern) (ha : d94642 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8927 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21343 q ha hb
    | true =>
      simp only [d8927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21336 q ha hb
  have h2 (q : Pattern) (ha : d8928 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8929 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8930 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8931 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94642 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21432 (p : Pattern) (ha : d94651 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9052 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9052, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9052, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d94648 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94649 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94650 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d94651 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21433 (p : Pattern) (ha : d94657 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94652 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21432 q ha hb
    | true =>
      simp only [d94652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21339 q ha hb
  have h2 (q : Pattern) (ha : d94653 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94654 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94655 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94656 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94657 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21434 (p : Pattern) (ha : d94663 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8933 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21342 q ha hb
    | true =>
      simp only [d8933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21344 q ha hb
  have h2 (q : Pattern) (ha : d8934 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94640 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94641 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94643 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21431 q ha hb
  have h6 (q : Pattern) (ha : d94644 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94645 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94646 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94647 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94658 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21433 q ha hb
  have h11 (q : Pattern) (ha : d94659 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94660 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94661 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94662 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94663 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro21435 (p : Pattern) (ha : d94669 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94664 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21434 q ha hb
  have h2 (q : Pattern) (ha : d94665 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94666 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94667 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94668 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94669 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21436 (p : Pattern) (ha : d94676 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9096 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21377 q ha hb
    | true =>
      simp only [d9096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21370 q ha hb
  have h2 (q : Pattern) (ha : d9097 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9098 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9099 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9100 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94676 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21437 (p : Pattern) (ha : d94685 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9220 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9221 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9221, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9221, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2386 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d100901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d94682 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94683 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94684 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d94685 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro21438 (p : Pattern) (ha : d94691 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94686 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21437 q ha hb
    | true =>
      simp only [d94686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21373 q ha hb
  have h2 (q : Pattern) (ha : d94687 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94688 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94689 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94690 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94691 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21439 (p : Pattern) (ha : d94697 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9102 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21376 q ha hb
    | true =>
      simp only [d9102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21378 q ha hb
  have h2 (q : Pattern) (ha : d9103 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94674 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94675 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94677 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21436 q ha hb
  have h6 (q : Pattern) (ha : d94678 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94679 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94680 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94681 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94692 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21438 q ha hb
  have h11 (q : Pattern) (ha : d94693 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94694 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94695 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94696 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94697 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro21440 (p : Pattern) (ha : d94703 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94698 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21439 q ha hb
  have h2 (q : Pattern) (ha : d94699 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94700 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94701 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94702 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94703 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21441 (p : Pattern) (ha : d94709 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d94574 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21415 q ha hb
    | true =>
      simp only [d94574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21420 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d94605 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21425 q ha hb
  have h3 (q : Pattern) (ha : d94606 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94637 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21430 q ha hb
  have h5 (q : Pattern) (ha : d94638 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94639 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94670 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21435 q ha hb
  have h8 (q : Pattern) (ha : d94671 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94672 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94673 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94704 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21440 q ha hb
  have h12 (q : Pattern) (ha : d94705 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94706 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94707 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94708 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d94708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94709 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d94709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro21442 (p : Pattern) (ha : d94715 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94710 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d94710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21441 q ha hb
    | true =>
      simp only [d94710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94711 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d94711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94712 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d94712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94713 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d94713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94714 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d94714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94715 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d94715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21443 (p : Pattern) (ha : d94721 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94716 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d94716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21442 q ha hb
    | true =>
      simp only [d94716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94717 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d94717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94718 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d94718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94719 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d94719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94720 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d94720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94721 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d94721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21444 (p : Pattern) (ha : d94727 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94722 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d94722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21443 q ha hb
    | true =>
      simp only [d94722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94723 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d94723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94724 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d94724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94725 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d94725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94726 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d94726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94727 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d94727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21445 (p : Pattern) (ha : d94733 p = 1) (hb : d100901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94728 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d94728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21444 q ha hb
    | true =>
      simp only [d94728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94729 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d94729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94730 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d94730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94731 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d94731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94732 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d94732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94733 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d94733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21446 (p : Pattern) (ha : d94739 p = 1) (hb : d100902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94734 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d94734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21445 q ha hb
    | true =>
      simp only [d94734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94735 q = 1) (hb : d100901 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d94735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d94736 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d94736, d100902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94736, d100902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d94737 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d94737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94738 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d94738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d94739 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d94739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro21447 (p : Pattern) (ha : d94745 p = 1) (hb : d100902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94740 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d94740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21446 q ha hb
    | true =>
      simp only [d94740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94741 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d94741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94742 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d94742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94743 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d94743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94744 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d94744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94745 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d94745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21448 (p : Pattern) (ha : d94751 p = 1) (hb : d100902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94746 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d94746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21447 q ha hb
    | true =>
      simp only [d94746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94747 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d94747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94748 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d94748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94749 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d94749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94750 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d94750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94751 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d94751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21449 (p : Pattern) (ha : d8238 p = 1) (hb : d92314 p = 1) : d8334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6741 q = 1) (hb : d92313 q = 1) : d6741 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8235 q = 1) (hb : d92314 q = 1) : d8331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8235, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8236 q = 1) (hb : d92314 q = 1) : d8332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d8332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8236, d8332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8237 q = 1) (hb : d92314 q = 1) : d8333 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8237, d8333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8237, d8333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8238 q = 1) (hb : d92314 q = 1) : d8334 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8238, d8334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8238, d8334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21450 (p : Pattern) (ha : d92314 p = 1) (hb : d94191 p = 1) : d93275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d92314 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d92314 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d92314 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8239 q = 1) (hb : d92314 q = 1) : d93270 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21449 q ha hb
    | true =>
      simp only [d8239, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94187 q = 1) : d93271 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94187, d93271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d94187, d93271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d92314 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94188 q = 1) : d93272 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94188, d93272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94188, d93272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d92314 q = 1) (hb : d94189 q = 1) : d93273 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94189, d93273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94189, d93273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92314 q = 1) (hb : d94190 q = 1) : d93274 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94190, d93274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94190, d93274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92314 q = 1) (hb : d94191 q = 1) : d93275 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94191, d93275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94191, d93275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro21451 (p : Pattern) (ha : d8245 p = 1) (hb : d92314 p = 1) : d8355 p = 1 := by
  have h0 (q : Pattern) (ha : d6741 q = 1) (hb : d92313 q = 1) : d6741 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8235 q = 1) (hb : d92314 q = 1) : d8331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8235, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8236 q = 1) (hb : d92314 q = 1) : d8332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d8332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8236, d8332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8237 q = 1) (hb : d92314 q = 1) : d8333 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8237, d8333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8237, d8333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8245 q = 1) (hb : d92314 q = 1) : d8355 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8245, d8355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8245, d8355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21452 (p : Pattern) (ha : d92314 p = 1) (hb : d94196 p = 1) : d93281 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d92314 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d92314 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d92314 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8239 q = 1) (hb : d92314 q = 1) : d93270 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21449 q ha hb
    | true =>
      simp only [d8239, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94187 q = 1) : d93271 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94187, d93271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d94187, d93271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d92314 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94188 q = 1) : d93272 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94188, d93272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94188, d93272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d92314 q = 1) (hb : d94189 q = 1) : d93273 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94189, d93273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94189, d93273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92314 q = 1) (hb : d94190 q = 1) : d93274 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94190, d93274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94190, d93274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d92314 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d92314 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d92314 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8246 q = 1) (hb : d92314 q = 1) : d93276 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21451 q ha hb
    | true =>
      simp only [d8246, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94192 q = 1) : d93277 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94192, d93277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d94192, d93277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d92314 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d92314 q = 1) (hb : d94193 q = 1) : d93278 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94193, d93278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94193, d93278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d92314 q = 1) (hb : d94194 q = 1) : d93279 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94194, d93279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d94194, d93279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92314 q = 1) (hb : d94195 q = 1) : d93280 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94195, d93280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94195, d93280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d92314 q = 1) (hb : d94196 q = 1) : d93281 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94196, d93281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94196, d93281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro21453 (p : Pattern) (ha : d92314 p = 1) (hb : d94203 p = 1) : d93288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d92314 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8246 q = 1) (hb : d92314 q = 1) : d93276 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21451 q ha hb
    | true =>
      simp only [d8246, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94192 q = 1) : d93277 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94192, d93277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94192, d93277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d92314 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94193 q = 1) : d93278 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94193, d93278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94193, d93278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94201 q = 1) : d93286 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94201, d93286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94201, d93286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94202 q = 1) : d93287 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94202, d93287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94202, d93287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92314 q = 1) (hb : d94203 q = 1) : d93288 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94203, d93288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94203, d93288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21454 (p : Pattern) (ha : d8267 p = 1) (hb : d92314 p = 1) : d8398 p = 1 := by
  have h0 (q : Pattern) (ha : d6774 q = 1) (hb : d92313 q = 1) : d6774 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8264 q = 1) (hb : d92314 q = 1) : d8395 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8264, d92314, d8395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8264, d92314, d8395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8265 q = 1) (hb : d92314 q = 1) : d8396 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8265, d8396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8265, d8396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8266 q = 1) (hb : d92314 q = 1) : d8397 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8266, d8397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8266, d8397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8267 q = 1) (hb : d92314 q = 1) : d8398 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8267, d8398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8267, d8398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21455 (p : Pattern) (ha : d92314 p = 1) (hb : d94213 p = 1) : d93299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d92314 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8268 q = 1) (hb : d92314 q = 1) : d93294 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8268, d93294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21454 q ha hb
    | true =>
      simp only [d8268, d93294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94209 q = 1) : d93295 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94209, d93295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94209, d93295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d92314 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94210 q = 1) : d93296 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94210, d93296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94210, d93296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94211 q = 1) : d93297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94211, d93297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94211, d93297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94212 q = 1) : d93298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94212, d93298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94212, d93298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92314 q = 1) (hb : d94213 q = 1) : d93299 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94213, d93299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94213, d93299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21456 (p : Pattern) (ha : d92314 p = 1) (hb : d94219 p = 1) : d93305 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d92314 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92314 q = 1) (hb : d94197 q = 1) : d93282 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94197, d93282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21450 q ha hb
    | true =>
      simp only [d94197, d93282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21452 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d92314 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94198 q = 1) : d93283 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94198, d93283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94198, d93283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94199 q = 1) : d93284 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94199, d93284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94199, d93284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94200 q = 1) : d93285 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94200, d93285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94200, d93285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94204 q = 1) : d93289 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94204, d93289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d94204, d93289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21453 q ha hb
  have h8 (q : Pattern) (ha : d92314 q = 1) (hb : d94205 q = 1) : d93290 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94205, d93290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94205, d93290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d92314 q = 1) (hb : d94206 q = 1) : d93291 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94206, d93291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94206, d93291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d92314 q = 1) (hb : d94207 q = 1) : d93292 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94207, d93292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94207, d93292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94208 q = 1) : d93293 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94208, d93293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94208, d93293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92314 q = 1) (hb : d94214 q = 1) : d93300 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94214, d93300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d94214, d93300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21455 q ha hb
  have h13 (q : Pattern) (ha : d92314 q = 1) (hb : d94215 q = 1) : d93301 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94215, d93301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94215, d93301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94216 q = 1) : d93302 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94216, d93302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94216, d93302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94217 q = 1) : d93303 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94217, d93303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94217, d93303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d92314 q = 1) (hb : d94218 q = 1) : d93304 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94218, d93304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94218, d93304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d92314 q = 1) (hb : d94219 q = 1) : d93305 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94219, d93305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94219, d93305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro21457 (p : Pattern) (ha : d8289 p = 1) (hb : d92314 p = 1) : d93315 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d92314 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8239 q = 1) (hb : d92314 q = 1) : d93270 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21449 q ha hb
    | true =>
      simp only [d8239, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8285 q = 1) (hb : d92314 q = 1) : d93311 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8285, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8286 q = 1) (hb : d92314 q = 1) : d93312 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8286, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8287 q = 1) (hb : d92314 q = 1) : d93313 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8287, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8288 q = 1) (hb : d92314 q = 1) : d93314 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8289 q = 1) (hb : d92314 q = 1) : d93315 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8289, d93315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8289, d93315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21458 (p : Pattern) (ha : d8296 p = 1) (hb : d92314 p = 1) : d93322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d92314 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8239 q = 1) (hb : d92314 q = 1) : d93270 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21449 q ha hb
    | true =>
      simp only [d8239, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8285 q = 1) (hb : d92314 q = 1) : d93311 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8285, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8286 q = 1) (hb : d92314 q = 1) : d93312 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8286, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8287 q = 1) (hb : d92314 q = 1) : d93313 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8287, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8288 q = 1) (hb : d92314 q = 1) : d93314 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d92314 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8246 q = 1) (hb : d92314 q = 1) : d93276 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21451 q ha hb
    | true =>
      simp only [d8246, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8292 q = 1) (hb : d92314 q = 1) : d93318 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8292, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8292, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8293 q = 1) (hb : d92314 q = 1) : d93319 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8293, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8293, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8294 q = 1) (hb : d92314 q = 1) : d93320 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8294, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8294, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d8295 q = 1) (hb : d92314 q = 1) : d93321 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8295, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8295, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d8296 q = 1) (hb : d92314 q = 1) : d93322 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8296, d93322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8296, d93322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro21459 (p : Pattern) (ha : d8363 p = 1) (hb : d92314 p = 1) : d93360 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d92314 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8239 q = 1) (hb : d92314 q = 1) : d93270 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21449 q ha hb
    | true =>
      simp only [d8239, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8285 q = 1) (hb : d92314 q = 1) : d93311 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8285, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8286 q = 1) (hb : d92314 q = 1) : d93312 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8286, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8287 q = 1) (hb : d92314 q = 1) : d93313 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8287, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8288 q = 1) (hb : d92314 q = 1) : d93314 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d92314 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8363 q = 1) (hb : d92314 q = 1) : d93360 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8363, d93360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8363, d93360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21460 (p : Pattern) (ha : d8301 p = 1) (hb : d92314 p = 1) : d93327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6741 q = 1) (hb : d92313 q = 1) : d6741 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8235 q = 1) (hb : d92314 q = 1) : d8331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8235, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8236 q = 1) (hb : d92314 q = 1) : d8332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d8332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8236, d8332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8300 q = 1) (hb : d92314 q = 1) : d93326 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8300, d93326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8300, d93326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8301 q = 1) (hb : d92314 q = 1) : d93327 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8301, d93327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8301, d93327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21461 (p : Pattern) (ha : d8308 p = 1) (hb : d92314 p = 1) : d93334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6741 q = 1) (hb : d92313 q = 1) : d6741 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8235 q = 1) (hb : d92314 q = 1) : d8331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8235, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8306 q = 1) (hb : d92314 q = 1) : d93332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8306, d93332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8306, d93332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8307 q = 1) (hb : d92314 q = 1) : d93333 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8307, d93333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8307, d93333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8308 q = 1) (hb : d92314 q = 1) : d93334 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8308, d93334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8308, d93334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21462 (p : Pattern) (ha : d8319 p = 1) (hb : d92314 p = 1) : d8479 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8315 q = 1) (hb : d92313 q = 1) : d8315 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6741 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8316 q = 1) (hb : d92314 q = 1) : d8476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8316, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8316, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8317 q = 1) (hb : d92314 q = 1) : d8477 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8317, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8317, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8318 q = 1) (hb : d92314 q = 1) : d8478 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8318, d8478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8318, d8478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8319 q = 1) (hb : d92314 q = 1) : d8479 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8319, d8479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8319, d8479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21463 (p : Pattern) (ha : d92314 p = 1) (hb : d94229 p = 1) : d93343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d92314 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8302 q = 1) (hb : d92314 q = 1) : d93328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8302, d93328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21460 q ha hb
    | true =>
      simp only [d8302, d93328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8303 q = 1) (hb : d92314 q = 1) : d93329 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8303, d93329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8303, d93329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8304 q = 1) (hb : d92314 q = 1) : d93330 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8304, d93330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8304, d93330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8305 q = 1) (hb : d92314 q = 1) : d93331 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8305, d93331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8305, d93331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d92314 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8309 q = 1) (hb : d92314 q = 1) : d93335 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8309, d93335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21461 q ha hb
    | true =>
      simp only [d8309, d93335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8310 q = 1) (hb : d92314 q = 1) : d93336 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8310, d93336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8310, d93336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8311 q = 1) (hb : d92314 q = 1) : d93337 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8311, d93337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8311, d93337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8320 q = 1) (hb : d92314 q = 1) : d93338 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8320, d93338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21462 q ha hb
    | true =>
      simp only [d8320, d93338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21449 q ha hb
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94225 q = 1) : d93339 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94225, d93339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94225, d93339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8336 q = 1) (hb : d92314 q = 1) : d8336 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d92314 q = 1) (hb : d94226 q = 1) : d93340 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94226, d93340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94226, d93340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94227 q = 1) : d93341 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94227, d93341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94227, d93341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94228 q = 1) : d93342 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94228, d93342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94228, d93342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92314 q = 1) (hb : d94229 q = 1) : d93343 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94229, d93343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94229, d93343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro21464 (p : Pattern) (ha : d8341 p = 1) (hb : d92314 p = 1) : d93344 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6741 q = 1) (hb : d92313 q = 1) : d6741 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8235 q = 1) (hb : d92314 q = 1) : d8331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8235, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8236 q = 1) (hb : d92314 q = 1) : d8332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d8332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8236, d8332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8300 q = 1) (hb : d92314 q = 1) : d93326 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8300, d93326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8300, d93326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8341 q = 1) (hb : d92314 q = 1) : d93344 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8341, d93344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8341, d93344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21465 (p : Pattern) (ha : d8346 p = 1) (hb : d92314 p = 1) : d93349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6741 q = 1) (hb : d92313 q = 1) : d6741 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8235 q = 1) (hb : d92314 q = 1) : d8331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8235, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8306 q = 1) (hb : d92314 q = 1) : d93332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8306, d93332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8306, d93332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8307 q = 1) (hb : d92314 q = 1) : d93333 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8307, d93333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8307, d93333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8346 q = 1) (hb : d92314 q = 1) : d93349 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8346, d93349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8346, d93349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21466 (p : Pattern) (ha : d8350 p = 1) (hb : d92314 p = 1) : d8501 p = 1 := by
  have h0 (q : Pattern) (ha : d8315 q = 1) (hb : d92313 q = 1) : d8315 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6741 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8316 q = 1) (hb : d92314 q = 1) : d8476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8316, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8316, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8317 q = 1) (hb : d92314 q = 1) : d8477 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8317, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8317, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8318 q = 1) (hb : d92314 q = 1) : d8478 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8318, d8478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8318, d8478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8350 q = 1) (hb : d92314 q = 1) : d8501 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8350, d8501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8350, d8501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21467 (p : Pattern) (ha : d92314 p = 1) (hb : d94234 p = 1) : d93358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d92314 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8302 q = 1) (hb : d92314 q = 1) : d93328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8302, d93328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21460 q ha hb
    | true =>
      simp only [d8302, d93328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8303 q = 1) (hb : d92314 q = 1) : d93329 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8303, d93329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8303, d93329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8304 q = 1) (hb : d92314 q = 1) : d93330 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8304, d93330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8304, d93330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8305 q = 1) (hb : d92314 q = 1) : d93331 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8305, d93331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8305, d93331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d92314 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8309 q = 1) (hb : d92314 q = 1) : d93335 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8309, d93335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21461 q ha hb
    | true =>
      simp only [d8309, d93335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8310 q = 1) (hb : d92314 q = 1) : d93336 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8310, d93336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8310, d93336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8311 q = 1) (hb : d92314 q = 1) : d93337 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8311, d93337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8311, d93337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8320 q = 1) (hb : d92314 q = 1) : d93338 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8320, d93338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21462 q ha hb
    | true =>
      simp only [d8320, d93338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21449 q ha hb
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94225 q = 1) : d93339 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94225, d93339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94225, d93339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8336 q = 1) (hb : d92314 q = 1) : d8336 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d92314 q = 1) (hb : d94226 q = 1) : d93340 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94226, d93340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94226, d93340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94227 q = 1) : d93341 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94227, d93341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94227, d93341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94228 q = 1) : d93342 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94228, d93342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94228, d93342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d194 q = 1) (hb : d92314 q = 1) : d194 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d8342 q = 1) (hb : d92314 q = 1) : d93345 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8342, d93345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21464 q ha hb
    | true =>
      simp only [d8342, d93345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8343 q = 1) (hb : d92314 q = 1) : d93346 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8343, d93346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8343, d93346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8344 q = 1) (hb : d92314 q = 1) : d93347 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8344, d93347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d8344, d93347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d8345 q = 1) (hb : d92314 q = 1) : d93348 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8345, d93348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8345, d93348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d199 q = 1) (hb : d92314 q = 1) : d199 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d8347 q = 1) (hb : d92314 q = 1) : d93350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8347, d93350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21465 q ha hb
    | true =>
      simp only [d8347, d93350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d8348 q = 1) (hb : d92314 q = 1) : d93351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8348, d93351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8348, d93351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d8349 q = 1) (hb : d92314 q = 1) : d93352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8349, d93352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d8349, d93352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8351 q = 1) (hb : d92314 q = 1) : d93353 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8351, d93353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21466 q ha hb
    | true =>
      simp only [d8351, d93353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21451 q ha hb
  have h26 (q : Pattern) (ha : d92314 q = 1) (hb : d94230 q = 1) : d93354 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94230, d93354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d94230, d93354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d8357 q = 1) (hb : d92314 q = 1) : d8357 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d92314 q = 1) (hb : d94231 q = 1) : d93355 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94231, d93355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d94231, d93355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d92314 q = 1) (hb : d94232 q = 1) : d93356 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94232, d93356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d94232, d93356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92314 q = 1) (hb : d94233 q = 1) : d93357 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94233, d93357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d94233, d93357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92314 q = 1) (hb : d94234 q = 1) : d93358 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94234, d93358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94234, d93358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro21468 (p : Pattern) (ha : d92314 p = 1) (hb : d94241 p = 1) : d93367 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8351 q = 1) (hb : d92314 q = 1) : d93353 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8351, d93353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21466 q ha hb
    | true =>
      simp only [d8351, d93353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21451 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94230 q = 1) : d93354 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94230, d93354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94230, d93354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d8357 q = 1) (hb : d92314 q = 1) : d8357 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94231 q = 1) : d93355 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94231, d93355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94231, d93355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94239 q = 1) : d93365 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94239, d93365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94239, d93365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94240 q = 1) : d93366 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94240, d93366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94240, d93366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94241 q = 1) : d93367 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94241, d93367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94241, d93367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21469 (p : Pattern) (ha : d8383 p = 1) (hb : d92314 p = 1) : d8555 p = 1 := by
  have h0 (q : Pattern) (ha : d8379 q = 1) (hb : d92313 q = 1) : d8379 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8380 q = 1) (hb : d92314 q = 1) : d8552 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8380, d92314, d8552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8380, d92314, d8552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8381 q = 1) (hb : d92314 q = 1) : d8553 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8381, d8553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8381, d8553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8382 q = 1) (hb : d92314 q = 1) : d8554 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8382, d8554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8382, d8554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8383 q = 1) (hb : d92314 q = 1) : d8555 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8383, d8555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8383, d8555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21470 (p : Pattern) (ha : d92314 p = 1) (hb : d94251 p = 1) : d93378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8384 q = 1) (hb : d92314 q = 1) : d93373 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8384, d93373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21469 q ha hb
    | true =>
      simp only [d8384, d93373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21454 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94247 q = 1) : d93374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94247, d93374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94247, d93374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d8400 q = 1) (hb : d92314 q = 1) : d8400 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94248 q = 1) : d93375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94248, d93375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94248, d93375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94249 q = 1) : d93376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94249, d93376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94249, d93376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94250 q = 1) : d93377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94250, d93377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94250, d93377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94251 q = 1) : d93378 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94251, d93378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94251, d93378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21471 (p : Pattern) (ha : d92314 p = 1) (hb : d94257 p = 1) : d93384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8290 q = 1) (hb : d92314 q = 1) : d93316 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8290, d93316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8290, d93316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21457 q ha hb
  have h2 (q : Pattern) (ha : d8291 q = 1) (hb : d92314 q = 1) : d93317 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8291, d93317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8291, d93317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8297 q = 1) (hb : d92314 q = 1) : d93323 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8297, d93323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21457 q ha hb
    | true =>
      simp only [d8297, d93323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21458 q ha hb
  have h4 (q : Pattern) (ha : d8298 q = 1) (hb : d92314 q = 1) : d93324 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8298, d93324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8298, d93324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8299 q = 1) (hb : d92314 q = 1) : d93325 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8299, d93325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8299, d93325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94235 q = 1) : d93359 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94235, d93359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21463 q ha hb
    | true =>
      simp only [d94235, d93359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21467 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d92314 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8364 q = 1) (hb : d92314 q = 1) : d93361 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8364, d93361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21459 q ha hb
    | true =>
      simp only [d8364, d93361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92314 q = 1) (hb : d94236 q = 1) : d93362 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94236, d93362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94236, d93362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92314 q = 1) (hb : d94237 q = 1) : d93363 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94237, d93363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94237, d93363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94238 q = 1) : d93364 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94238, d93364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94238, d93364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92314 q = 1) (hb : d94242 q = 1) : d93368 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94242, d93368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94242, d93368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21468 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d92314 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94243 q = 1) : d93369 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94243, d93369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94243, d93369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94244 q = 1) : d93370 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94244, d93370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94244, d93370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92314 q = 1) (hb : d94245 q = 1) : d93371 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94245, d93371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94245, d93371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d92314 q = 1) (hb : d94246 q = 1) : d93372 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94246, d93372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94246, d93372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92314 q = 1) (hb : d94252 q = 1) : d93379 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94252, d93379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94252, d93379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21470 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d92314 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d92314 q = 1) (hb : d94253 q = 1) : d93380 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94253, d93380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94253, d93380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d92314 q = 1) (hb : d94254 q = 1) : d93381 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94254, d93381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94254, d93381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92314 q = 1) (hb : d94255 q = 1) : d93382 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94255, d93382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94255, d93382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92314 q = 1) (hb : d94256 q = 1) : d93383 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94256, d93383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94256, d93383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d92314 q = 1) (hb : d94257 q = 1) : d93384 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94257, d93384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94257, d93384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro21472 (p : Pattern) (ha : d92314 p = 1) (hb : d94263 p = 1) : d93390 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d92314 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94220 q = 1) : d93306 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94220, d93306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94220, d93306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21456 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94221 q = 1) : d93307 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94221, d93307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94221, d93307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94222 q = 1) : d93308 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94222, d93308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94222, d93308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94223 q = 1) : d93309 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94223, d93309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94223, d93309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94224 q = 1) : d93310 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94224, d93310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94224, d93310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94258 q = 1) : d93385 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94258, d93385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94258, d93385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21471 q ha hb
  have h8 (q : Pattern) (ha : d92314 q = 1) (hb : d94259 q = 1) : d93386 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94259, d93386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94259, d93386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92314 q = 1) (hb : d94260 q = 1) : d93387 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94260, d93387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94260, d93387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92314 q = 1) (hb : d94261 q = 1) : d93388 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94261, d93388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94261, d93388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94262 q = 1) : d93389 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94262, d93389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94262, d93389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92314 q = 1) (hb : d94263 q = 1) : d93390 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94263, d93390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94263, d93390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro21473 (p : Pattern) (ha : d8420 p = 1) (hb : d92314 p = 1) : d8479 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8315 q = 1) (hb : d92313 q = 1) : d8315 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d483 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8417 q = 1) (hb : d92314 q = 1) : d8476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8417, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8418 q = 1) (hb : d92314 q = 1) : d8477 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8418, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8419 q = 1) (hb : d92314 q = 1) : d8478 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8419, d8478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8419, d8478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8420 q = 1) (hb : d92314 q = 1) : d8479 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8420, d8479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8420, d8479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21474 (p : Pattern) (ha : d8426 p = 1) (hb : d92314 p = 1) : d93396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d92314 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8421 q = 1) (hb : d92314 q = 1) : d93391 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8421, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21473 q ha hb
    | true =>
      simp only [d8421, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8422 q = 1) (hb : d92314 q = 1) : d93392 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8422, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8422, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8423 q = 1) (hb : d92314 q = 1) : d93393 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8423, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8423, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8424 q = 1) (hb : d92314 q = 1) : d93394 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8424, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8424, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8425 q = 1) (hb : d92314 q = 1) : d93395 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8425, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8425, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8426 q = 1) (hb : d92314 q = 1) : d93396 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8426, d93396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8426, d93396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21475 (p : Pattern) (ha : d8429 p = 1) (hb : d92314 p = 1) : d8501 p = 1 := by
  have h0 (q : Pattern) (ha : d8315 q = 1) (hb : d92313 q = 1) : d8315 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d483 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8417 q = 1) (hb : d92314 q = 1) : d8476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8417, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8418 q = 1) (hb : d92314 q = 1) : d8477 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8418, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8419 q = 1) (hb : d92314 q = 1) : d8478 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8419, d8478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8419, d8478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8429 q = 1) (hb : d92314 q = 1) : d8501 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8429, d8501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8429, d8501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21476 (p : Pattern) (ha : d8435 p = 1) (hb : d92314 p = 1) : d93404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d92314 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8421 q = 1) (hb : d92314 q = 1) : d93391 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8421, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21473 q ha hb
    | true =>
      simp only [d8421, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8422 q = 1) (hb : d92314 q = 1) : d93392 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8422, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8422, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8423 q = 1) (hb : d92314 q = 1) : d93393 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8423, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8423, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8424 q = 1) (hb : d92314 q = 1) : d93394 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8424, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8424, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8425 q = 1) (hb : d92314 q = 1) : d93395 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8425, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8425, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d501 q = 1) (hb : d92314 q = 1) : d501 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8430 q = 1) (hb : d92314 q = 1) : d93399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8430, d93399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21475 q ha hb
    | true =>
      simp only [d8430, d93399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8431 q = 1) (hb : d92314 q = 1) : d93400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8431, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8431, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8432 q = 1) (hb : d92314 q = 1) : d93401 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8432, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8432, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8433 q = 1) (hb : d92314 q = 1) : d93402 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8433, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8433, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d8434 q = 1) (hb : d92314 q = 1) : d93403 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8434, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8434, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d8435 q = 1) (hb : d92314 q = 1) : d93404 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8435, d93404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8435, d93404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro21477 (p : Pattern) (ha : d8463 p = 1) (hb : d92314 p = 1) : d93427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6801 q = 1) (hb : d92313 q = 1) : d6801 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d483 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8460 q = 1) (hb : d92314 q = 1) : d93424 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8460, d92314, d93424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8460, d92314, d93424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8461 q = 1) (hb : d92314 q = 1) : d93425 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8461, d93425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8461, d93425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8462 q = 1) (hb : d92314 q = 1) : d93426 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8462, d93426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8462, d93426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8463 q = 1) (hb : d92314 q = 1) : d93427 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8463, d93427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8463, d93427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21478 (p : Pattern) (ha : d8514 p = 1) (hb : d92314 p = 1) : d93457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d92314 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8509 q = 1) (hb : d92314 q = 1) : d93452 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8509, d93452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21477 q ha hb
    | true =>
      simp only [d8509, d93452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8510 q = 1) (hb : d92314 q = 1) : d93453 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8510, d93453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8510, d93453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8511 q = 1) (hb : d92314 q = 1) : d93454 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8511, d93454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8511, d93454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8512 q = 1) (hb : d92314 q = 1) : d93455 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8512, d93455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8512, d93455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8513 q = 1) (hb : d92314 q = 1) : d93456 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8513, d93456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8513, d93456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d637 q = 1) (hb : d92314 q = 1) : d637 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8514 q = 1) (hb : d92314 q = 1) : d93457 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8514, d93457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8514, d93457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21479 (p : Pattern) (ha : d8440 p = 1) (hb : d92314 p = 1) : d93409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8315 q = 1) (hb : d92313 q = 1) : d8315 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d483 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8417 q = 1) (hb : d92314 q = 1) : d8476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8417, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8418 q = 1) (hb : d92314 q = 1) : d8477 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8418, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8439 q = 1) (hb : d92314 q = 1) : d93408 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8439, d93408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8439, d93408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8440 q = 1) (hb : d92314 q = 1) : d93409 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8440, d93409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8440, d93409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21480 (p : Pattern) (ha : d8447 p = 1) (hb : d92314 p = 1) : d93416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8315 q = 1) (hb : d92313 q = 1) : d8315 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d483 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8417 q = 1) (hb : d92314 q = 1) : d8476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8417, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8445 q = 1) (hb : d92314 q = 1) : d93414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8445, d93414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8445, d93414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8446 q = 1) (hb : d92314 q = 1) : d93415 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8446, d93415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8446, d93415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8447 q = 1) (hb : d92314 q = 1) : d93416 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8447, d93416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8447, d93416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21481 (p : Pattern) (ha : d8459 p = 1) (hb : d92314 p = 1) : d93423 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8455 q = 1) (hb : d92313 q = 1) : d8455 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6801 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8456 q = 1) (hb : d92314 q = 1) : d93420 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8456, d92314, d93420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8456, d92314, d93420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8457 q = 1) (hb : d92314 q = 1) : d93421 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8457, d93421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8457, d93421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8458 q = 1) (hb : d92314 q = 1) : d93422 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8458, d93422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8458, d93422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8459 q = 1) (hb : d92314 q = 1) : d93423 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8459, d93423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8459, d93423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21482 (p : Pattern) (ha : d92314 p = 1) (hb : d94268 p = 1) : d93433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d514 q = 1) (hb : d92314 q = 1) : d514 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8441 q = 1) (hb : d92314 q = 1) : d93410 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8441, d93410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21479 q ha hb
    | true =>
      simp only [d8441, d93410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8442 q = 1) (hb : d92314 q = 1) : d93411 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8442, d93411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8442, d93411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8443 q = 1) (hb : d92314 q = 1) : d93412 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8443, d93412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8443, d93412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8444 q = 1) (hb : d92314 q = 1) : d93413 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8444, d93413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8444, d93413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d92314 q = 1) : d524 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8448 q = 1) (hb : d92314 q = 1) : d93417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8448, d93417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21480 q ha hb
    | true =>
      simp only [d8448, d93417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8449 q = 1) (hb : d92314 q = 1) : d93418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8449, d93418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8449, d93418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8450 q = 1) (hb : d92314 q = 1) : d93419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8450, d93419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8450, d93419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8464 q = 1) (hb : d92314 q = 1) : d93428 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8464, d93428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21481 q ha hb
    | true =>
      simp only [d8464, d93428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21477 q ha hb
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94264 q = 1) : d93429 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94264, d93429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94264, d93429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8481 q = 1) (hb : d92314 q = 1) : d8481 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d92314 q = 1) (hb : d94265 q = 1) : d93430 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94265, d93430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94265, d93430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94266 q = 1) : d93431 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94266, d93431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94266, d93431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94267 q = 1) : d93432 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94267, d93432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94267, d93432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92314 q = 1) (hb : d94268 q = 1) : d93433 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94268, d93433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94268, d93433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro21483 (p : Pattern) (ha : d8486 p = 1) (hb : d92314 p = 1) : d93434 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8315 q = 1) (hb : d92313 q = 1) : d8315 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d483 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8417 q = 1) (hb : d92314 q = 1) : d8476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8417, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8418 q = 1) (hb : d92314 q = 1) : d8477 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8418, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8439 q = 1) (hb : d92314 q = 1) : d93408 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8439, d93408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8439, d93408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8486 q = 1) (hb : d92314 q = 1) : d93434 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8486, d93434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8486, d93434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21484 (p : Pattern) (ha : d8491 p = 1) (hb : d92314 p = 1) : d93439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8315 q = 1) (hb : d92313 q = 1) : d8315 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d483 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8417 q = 1) (hb : d92314 q = 1) : d8476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8417, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8445 q = 1) (hb : d92314 q = 1) : d93414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8445, d93414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8445, d93414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8446 q = 1) (hb : d92314 q = 1) : d93415 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8446, d93415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8446, d93415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8491 q = 1) (hb : d92314 q = 1) : d93439 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8491, d93439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8491, d93439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21485 (p : Pattern) (ha : d8495 p = 1) (hb : d92314 p = 1) : d93443 p = 1 := by
  have h0 (q : Pattern) (ha : d8455 q = 1) (hb : d92313 q = 1) : d8455 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6801 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8456 q = 1) (hb : d92314 q = 1) : d93420 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8456, d92314, d93420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8456, d92314, d93420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8457 q = 1) (hb : d92314 q = 1) : d93421 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8457, d93421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8457, d93421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8458 q = 1) (hb : d92314 q = 1) : d93422 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8458, d93422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8458, d93422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8495 q = 1) (hb : d92314 q = 1) : d93443 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8495, d93443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8495, d93443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21486 (p : Pattern) (ha : d8496 p = 1) (hb : d92314 p = 1) : d93444 p = 1 := by
  have h0 (q : Pattern) (ha : d6801 q = 1) (hb : d92313 q = 1) : d6801 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d483 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8460 q = 1) (hb : d92314 q = 1) : d93424 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8460, d92314, d93424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8460, d92314, d93424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8461 q = 1) (hb : d92314 q = 1) : d93425 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8461, d93425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8461, d93425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8462 q = 1) (hb : d92314 q = 1) : d93426 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8462, d93426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8462, d93426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8496 q = 1) (hb : d92314 q = 1) : d93444 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8496, d93444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8496, d93444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21487 (p : Pattern) (ha : d92314 p = 1) (hb : d94273 p = 1) : d93450 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d514 q = 1) (hb : d92314 q = 1) : d514 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8441 q = 1) (hb : d92314 q = 1) : d93410 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8441, d93410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21479 q ha hb
    | true =>
      simp only [d8441, d93410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8442 q = 1) (hb : d92314 q = 1) : d93411 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8442, d93411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8442, d93411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8443 q = 1) (hb : d92314 q = 1) : d93412 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8443, d93412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8443, d93412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8444 q = 1) (hb : d92314 q = 1) : d93413 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8444, d93413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8444, d93413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d92314 q = 1) : d524 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8448 q = 1) (hb : d92314 q = 1) : d93417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8448, d93417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21480 q ha hb
    | true =>
      simp only [d8448, d93417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8449 q = 1) (hb : d92314 q = 1) : d93418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8449, d93418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8449, d93418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8450 q = 1) (hb : d92314 q = 1) : d93419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8450, d93419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8450, d93419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8464 q = 1) (hb : d92314 q = 1) : d93428 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8464, d93428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21481 q ha hb
    | true =>
      simp only [d8464, d93428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21477 q ha hb
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94264 q = 1) : d93429 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94264, d93429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94264, d93429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8481 q = 1) (hb : d92314 q = 1) : d8481 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d92314 q = 1) (hb : d94265 q = 1) : d93430 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94265, d93430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94265, d93430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94266 q = 1) : d93431 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94266, d93431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94266, d93431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94267 q = 1) : d93432 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94267, d93432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94267, d93432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d610 q = 1) (hb : d92314 q = 1) : d610 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d8487 q = 1) (hb : d92314 q = 1) : d93435 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8487, d93435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21483 q ha hb
    | true =>
      simp only [d8487, d93435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8488 q = 1) (hb : d92314 q = 1) : d93436 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8488, d93436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8488, d93436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8489 q = 1) (hb : d92314 q = 1) : d93437 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8489, d93437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d8489, d93437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d8490 q = 1) (hb : d92314 q = 1) : d93438 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8490, d93438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8490, d93438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d616 q = 1) (hb : d92314 q = 1) : d616 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d8492 q = 1) (hb : d92314 q = 1) : d93440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8492, d93440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21484 q ha hb
    | true =>
      simp only [d8492, d93440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d8493 q = 1) (hb : d92314 q = 1) : d93441 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8493, d93441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8493, d93441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d8494 q = 1) (hb : d92314 q = 1) : d93442 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8494, d93442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d8494, d93442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8497 q = 1) (hb : d92314 q = 1) : d93445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8497, d93445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21485 q ha hb
    | true =>
      simp only [d8497, d93445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21486 q ha hb
  have h26 (q : Pattern) (ha : d92314 q = 1) (hb : d94269 q = 1) : d93446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94269, d93446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d94269, d93446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d8503 q = 1) (hb : d92314 q = 1) : d8503 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d92314 q = 1) (hb : d94270 q = 1) : d93447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94270, d93447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d94270, d93447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d92314 q = 1) (hb : d94271 q = 1) : d93448 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94271, d93448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d94271, d93448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92314 q = 1) (hb : d94272 q = 1) : d93449 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94272, d93449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d94272, d93449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92314 q = 1) (hb : d94273 q = 1) : d93450 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94273, d93450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94273, d93450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro21488 (p : Pattern) (ha : d92314 p = 1) (hb : d94280 p = 1) : d93464 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8497 q = 1) (hb : d92314 q = 1) : d93445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8497, d93445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21485 q ha hb
    | true =>
      simp only [d8497, d93445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21486 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94269 q = 1) : d93446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94269, d93446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94269, d93446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d8503 q = 1) (hb : d92314 q = 1) : d8503 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94270 q = 1) : d93447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94270, d93447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94270, d93447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94278 q = 1) : d93462 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94278, d93462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94278, d93462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94279 q = 1) : d93463 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94279, d93463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94279, d93463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94280 q = 1) : d93464 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94280, d93464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94280, d93464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21489 (p : Pattern) (ha : d8535 p = 1) (hb : d92314 p = 1) : d93473 p = 1 := by
  have h0 (q : Pattern) (ha : d8531 q = 1) (hb : d92313 q = 1) : d8531 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6847 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8532 q = 1) (hb : d92314 q = 1) : d93470 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8532, d92314, d93470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8532, d92314, d93470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8533 q = 1) (hb : d92314 q = 1) : d93471 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8533, d93471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8533, d93471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8534 q = 1) (hb : d92314 q = 1) : d93472 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8534, d93472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8534, d93472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8535 q = 1) (hb : d92314 q = 1) : d93473 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8535, d93473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8535, d93473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21490 (p : Pattern) (ha : d8539 p = 1) (hb : d92314 p = 1) : d93477 p = 1 := by
  have h0 (q : Pattern) (ha : d6847 q = 1) (hb : d92313 q = 1) : d6847 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d685 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8536 q = 1) (hb : d92314 q = 1) : d93474 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8536, d92314, d93474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8536, d92314, d93474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8537 q = 1) (hb : d92314 q = 1) : d93475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8537, d93475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8537, d93475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8538 q = 1) (hb : d92314 q = 1) : d93476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8538, d93476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8538, d93476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8539 q = 1) (hb : d92314 q = 1) : d93477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8539, d93477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8539, d93477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21491 (p : Pattern) (ha : d92314 p = 1) (hb : d94290 p = 1) : d93483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8540 q = 1) (hb : d92314 q = 1) : d93478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8540, d93478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21489 q ha hb
    | true =>
      simp only [d8540, d93478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21490 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94286 q = 1) : d93479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94286, d93479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94286, d93479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d8557 q = 1) (hb : d92314 q = 1) : d8557 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94287 q = 1) : d93480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94287, d93480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94287, d93480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94288 q = 1) : d93481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94288, d93481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94288, d93481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94289 q = 1) : d93482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94289, d93482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94289, d93482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94290 q = 1) : d93483 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94290, d93483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94290, d93483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21492 (p : Pattern) (ha : d92314 p = 1) (hb : d94296 p = 1) : d93489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8427 q = 1) (hb : d92314 q = 1) : d93397 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8427, d93397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8427, d93397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21474 q ha hb
  have h2 (q : Pattern) (ha : d8428 q = 1) (hb : d92314 q = 1) : d93398 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8428, d93398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8428, d93398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8436 q = 1) (hb : d92314 q = 1) : d93405 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8436, d93405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21474 q ha hb
    | true =>
      simp only [d8436, d93405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21476 q ha hb
  have h4 (q : Pattern) (ha : d8437 q = 1) (hb : d92314 q = 1) : d93406 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8437, d93406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8437, d93406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8438 q = 1) (hb : d92314 q = 1) : d93407 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8438, d93407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8438, d93407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94274 q = 1) : d93451 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94274, d93451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21482 q ha hb
    | true =>
      simp only [d94274, d93451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21487 q ha hb
  have h7 (q : Pattern) (ha : d644 q = 1) (hb : d92314 q = 1) : d644 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8515 q = 1) (hb : d92314 q = 1) : d93458 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8515, d93458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21478 q ha hb
    | true =>
      simp only [d8515, d93458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92314 q = 1) (hb : d94275 q = 1) : d93459 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94275, d93459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94275, d93459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92314 q = 1) (hb : d94276 q = 1) : d93460 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94276, d93460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94276, d93460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94277 q = 1) : d93461 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94277, d93461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94277, d93461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92314 q = 1) (hb : d94281 q = 1) : d93465 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94281, d93465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94281, d93465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21488 q ha hb
  have h13 (q : Pattern) (ha : d654 q = 1) (hb : d92314 q = 1) : d654 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94282 q = 1) : d93466 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94282, d93466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94282, d93466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94283 q = 1) : d93467 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94283, d93467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94283, d93467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92314 q = 1) (hb : d94284 q = 1) : d93468 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94284, d93468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94284, d93468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d92314 q = 1) (hb : d94285 q = 1) : d93469 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94285, d93469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94285, d93469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92314 q = 1) (hb : d94291 q = 1) : d93484 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94291, d93484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94291, d93484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21491 q ha hb
  have h19 (q : Pattern) (ha : d737 q = 1) (hb : d92314 q = 1) : d737 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d92314 q = 1) (hb : d94292 q = 1) : d93485 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94292, d93485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94292, d93485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d92314 q = 1) (hb : d94293 q = 1) : d93486 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94293, d93486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94293, d93486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92314 q = 1) (hb : d94294 q = 1) : d93487 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94294, d93487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94294, d93487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92314 q = 1) (hb : d94295 q = 1) : d93488 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94295, d93488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94295, d93488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d92314 q = 1) (hb : d94296 q = 1) : d93489 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94296, d93489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94296, d93489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro21493 (p : Pattern) (ha : d92314 p = 1) (hb : d94302 p = 1) : d93495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92314 q = 1) (hb : d94297 q = 1) : d93490 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94297, d93490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94297, d93490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21492 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94298 q = 1) : d93491 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94298, d93491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94298, d93491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94299 q = 1) : d93492 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94299, d93492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94299, d93492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94300 q = 1) : d93493 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94300, d93493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94300, d93493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94301 q = 1) : d93494 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94301, d93494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94301, d93494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94302 q = 1) : d93495 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94302, d93495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94302, d93495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21494 (p : Pattern) (ha : d8582 p = 1) (hb : d92314 p = 1) : d8641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8578 q = 1) (hb : d92313 q = 1) : d8578 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d775 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8579 q = 1) (hb : d92314 q = 1) : d8638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8579, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8580 q = 1) (hb : d92314 q = 1) : d8639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, d8639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8580, d8639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8581 q = 1) (hb : d92314 q = 1) : d8640 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8581, d8640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8581, d8640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8582 q = 1) (hb : d92314 q = 1) : d8641 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8582, d8641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8582, d8641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21495 (p : Pattern) (ha : d8588 p = 1) (hb : d92314 p = 1) : d93502 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d92314 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8583 q = 1) (hb : d92314 q = 1) : d93497 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8583, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21494 q ha hb
    | true =>
      simp only [d8583, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8584 q = 1) (hb : d92314 q = 1) : d93498 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8584, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8584, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8585 q = 1) (hb : d92314 q = 1) : d93499 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8585, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8585, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8586 q = 1) (hb : d92314 q = 1) : d93500 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8586, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8586, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8587 q = 1) (hb : d92314 q = 1) : d93501 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8587, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8587, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8588 q = 1) (hb : d92314 q = 1) : d93502 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8588, d93502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8588, d93502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21496 (p : Pattern) (ha : d8591 p = 1) (hb : d92314 p = 1) : d8663 p = 1 := by
  have h0 (q : Pattern) (ha : d8578 q = 1) (hb : d92313 q = 1) : d8578 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d775 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8579 q = 1) (hb : d92314 q = 1) : d8638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8579, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8580 q = 1) (hb : d92314 q = 1) : d8639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, d8639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8580, d8639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8581 q = 1) (hb : d92314 q = 1) : d8640 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8581, d8640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8581, d8640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8591 q = 1) (hb : d92314 q = 1) : d8663 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8591, d8663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8591, d8663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21497 (p : Pattern) (ha : d8597 p = 1) (hb : d92314 p = 1) : d93510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d92314 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8583 q = 1) (hb : d92314 q = 1) : d93497 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8583, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21494 q ha hb
    | true =>
      simp only [d8583, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8584 q = 1) (hb : d92314 q = 1) : d93498 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8584, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8584, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8585 q = 1) (hb : d92314 q = 1) : d93499 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8585, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8585, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8586 q = 1) (hb : d92314 q = 1) : d93500 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8586, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8586, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8587 q = 1) (hb : d92314 q = 1) : d93501 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8587, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8587, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d793 q = 1) (hb : d92314 q = 1) : d793 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8592 q = 1) (hb : d92314 q = 1) : d93505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8592, d93505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21496 q ha hb
    | true =>
      simp only [d8592, d93505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8593 q = 1) (hb : d92314 q = 1) : d93506 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8593, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8593, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8594 q = 1) (hb : d92314 q = 1) : d93507 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8594, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8594, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8595 q = 1) (hb : d92314 q = 1) : d93508 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8595, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8595, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d8596 q = 1) (hb : d92314 q = 1) : d93509 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8596, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8596, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d8597 q = 1) (hb : d92314 q = 1) : d93510 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8597, d93510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8597, d93510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro21498 (p : Pattern) (ha : d8625 p = 1) (hb : d92314 p = 1) : d93533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6879 q = 1) (hb : d92313 q = 1) : d6879 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d775 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8622 q = 1) (hb : d92314 q = 1) : d93530 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8622, d92314, d93530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8622, d92314, d93530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8623 q = 1) (hb : d92314 q = 1) : d93531 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8623, d93531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8623, d93531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8624 q = 1) (hb : d92314 q = 1) : d93532 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8624, d93532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8624, d93532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8625 q = 1) (hb : d92314 q = 1) : d93533 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8625, d93533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8625, d93533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21499 (p : Pattern) (ha : d8676 p = 1) (hb : d92314 p = 1) : d93563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d92314 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8671 q = 1) (hb : d92314 q = 1) : d93558 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8671, d93558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21498 q ha hb
    | true =>
      simp only [d8671, d93558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8672 q = 1) (hb : d92314 q = 1) : d93559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8672, d93559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8672, d93559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8673 q = 1) (hb : d92314 q = 1) : d93560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8673, d93560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8673, d93560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8674 q = 1) (hb : d92314 q = 1) : d93561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8674, d93561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8674, d93561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8675 q = 1) (hb : d92314 q = 1) : d93562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8675, d93562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8675, d93562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d943 q = 1) (hb : d92314 q = 1) : d943 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8676 q = 1) (hb : d92314 q = 1) : d93563 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8676, d93563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8676, d93563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
