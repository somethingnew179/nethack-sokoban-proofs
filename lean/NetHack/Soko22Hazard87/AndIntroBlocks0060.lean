import NetHack.Soko22Hazard87.AndIntroBlocks0059
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro15000 (p : Pattern) (ha : d105707 p = 1) (hb : d106401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105702 q = 1) (hb : d106396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105702, d106396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14999 q ha hb
    | true =>
      simp only [d105702, d106396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105703 q = 1) (hb : d106397 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105703, d106397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105703, d106397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105704 q = 1) (hb : d106398 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105704, d106398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105704, d106398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105705 q = 1) (hb : d106399 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105705, d106399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105705, d106399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105706 q = 1) (hb : d106400 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105706, d106400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105706, d106400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105707 q = 1) (hb : d106401 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105707, d106401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105707, d106401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15001 (p : Pattern) (ha : d105710 p = 1) (hb : d106404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105696 q = 1) (hb : d106390 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105696, d106390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14998 q ha hb
    | true =>
      simp only [d105696, d106390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105697 q = 1) (hb : d106391 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105697, d106391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105697, d106391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105698 q = 1) (hb : d106392 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105698, d106392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105698, d106392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105699 q = 1) (hb : d106393 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105699, d106393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105699, d106393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105700 q = 1) (hb : d106394 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105700, d106394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105700, d106394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105710 q = 1) (hb : d106404 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105710, d106404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105710, d106404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15002 (p : Pattern) (ha : d105716 p = 1) (hb : d106410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105702 q = 1) (hb : d106396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105702, d106396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14999 q ha hb
    | true =>
      simp only [d105702, d106396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105703 q = 1) (hb : d106397 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105703, d106397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105703, d106397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105704 q = 1) (hb : d106398 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105704, d106398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105704, d106398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105705 q = 1) (hb : d106399 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105705, d106399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105705, d106399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105706 q = 1) (hb : d106400 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105706, d106400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105706, d106400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105711 q = 1) (hb : d106405 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105711, d106405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15001 q ha hb
    | true =>
      simp only [d105711, d106405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d105712 q = 1) (hb : d106406 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105712, d106406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105712, d106406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d105713 q = 1) (hb : d106407 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105713, d106407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d105713, d106407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d105714 q = 1) (hb : d106408 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105714, d106408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105714, d106408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d105715 q = 1) (hb : d106409 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105715, d106409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105715, d106409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d105716 q = 1) (hb : d106410 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105716, d106410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105716, d106410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15003 (p : Pattern) (ha : d5450 p = 1) (hb : d52427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d134 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5448 q = 1) (hb : d51987 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d51987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5448, d51987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5449 q = 1) (hb : d51988 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d51988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5449, d51988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d5450 q = 1) (hb : d52427 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5450, d52427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5450, d52427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro15004 (p : Pattern) (ha : d5456 p = 1) (hb : d52435 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d755 q = 1) (hb : d52432 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d52432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d755, d52432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5451 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15003 q ha hb
    | true =>
      simp only [d5451, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5452 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5452, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5453 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5454 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5454, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d5455 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5455, d52434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5455, d52434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d5456 q = 1) (hb : d52435 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5456, d52435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5456, d52435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro15005 (p : Pattern) (ha : d5457 p = 1) (hb : d52439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5451 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15003 q ha hb
    | true =>
      simp only [d5451, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5452 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5452, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5453 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5454 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5454, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5455 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5455, d52434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5455, d52434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5457 q = 1) (hb : d52439 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5457, d52439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5457, d52439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15006 (p : Pattern) (ha : d105695 p = 1) (hb : d106437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52442 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5458 q = 1) (hb : d52440 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5458, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15004 q ha hb
    | true =>
      simp only [d5458, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15005 q ha hb
  have h3 (q : Pattern) (ha : d5459 q = 1) (hb : d52441 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5459, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5459, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5460 q = 1) (hb : d52442 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5460, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5460, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5461 q = 1) (hb : d52442 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52442 q = 1) (hb : d106436 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d105695 q = 1) (hb : d106437 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105695, d106437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105695, d106437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15007 (p : Pattern) (ha : d105701 p = 1) (hb : d106443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105696 q = 1) (hb : d106438 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105696, d106438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15006 q ha hb
    | true =>
      simp only [d105696, d106438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105697 q = 1) (hb : d106439 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105697, d106439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105697, d106439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105698 q = 1) (hb : d106440 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105698, d106440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105698, d106440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105699 q = 1) (hb : d106441 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105699, d106441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105699, d106441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105700 q = 1) (hb : d106442 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105700, d106442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105700, d106442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105701 q = 1) (hb : d106443 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105701, d106443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105701, d106443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15008 (p : Pattern) (ha : d105721 p = 1) (hb : d106415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105696 q = 1) (hb : d106390 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105696, d106390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14998 q ha hb
    | true =>
      simp only [d105696, d106390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105697 q = 1) (hb : d106391 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105697, d106391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105697, d106391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105698 q = 1) (hb : d106392 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105698, d106392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105698, d106392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105699 q = 1) (hb : d106393 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105699, d106393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105699, d106393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105720 q = 1) (hb : d106414 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105720, d106414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105720, d106414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105721 q = 1) (hb : d106415 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105721, d106415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105721, d106415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15009 (p : Pattern) (ha : d105728 p = 1) (hb : d106422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105696 q = 1) (hb : d106390 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105696, d106390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14998 q ha hb
    | true =>
      simp only [d105696, d106390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105697 q = 1) (hb : d106391 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105697, d106391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105697, d106391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105698 q = 1) (hb : d106392 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105698, d106392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105698, d106392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105726 q = 1) (hb : d106420 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105726, d106420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105726, d106420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105727 q = 1) (hb : d106421 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105727, d106421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105727, d106421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105728 q = 1) (hb : d106422 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105728, d106422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105728, d106422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15010 (p : Pattern) (ha : d105732 p = 1) (hb : d106427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52438 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d759 q = 1) (hb : d52436 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
    | true =>
      simp only [d759, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
  have h3 (q : Pattern) (ha : d760 q = 1) (hb : d52437 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d760, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d761 q = 1) (hb : d52438 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d761, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6875 q = 1) (hb : d52438 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52438 q = 1) (hb : d106426 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d105732 q = 1) (hb : d106427 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105732, d106427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105732, d106427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15011 (p : Pattern) (ha : d105738 p = 1) (hb : d106433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105733 q = 1) (hb : d106428 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105733, d106428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15010 q ha hb
    | true =>
      simp only [d105733, d106428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105734 q = 1) (hb : d106429 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105734, d106429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105734, d106429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105696 q = 1) (hb : d106390 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105696, d106390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14998 q ha hb
    | true =>
      simp only [d105696, d106390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105697 q = 1) (hb : d106391 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105697, d106391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105697, d106391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105735 q = 1) (hb : d106430 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105735, d106430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105735, d106430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105736 q = 1) (hb : d106431 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105736, d106431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105736, d106431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d105737 q = 1) (hb : d106432 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105737, d106432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105737, d106432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d105738 q = 1) (hb : d106433 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105738, d106433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105738, d106433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15012 (p : Pattern) (ha : d105745 p = 1) (hb : d106449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105722 q = 1) (hb : d106416 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105722, d106416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15008 q ha hb
    | true =>
      simp only [d105722, d106416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105723 q = 1) (hb : d106417 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105723, d106417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105723, d106417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105724 q = 1) (hb : d106418 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105724, d106418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105724, d106418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105725 q = 1) (hb : d106419 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105725, d106419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105725, d106419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105729 q = 1) (hb : d106423 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105729, d106423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15009 q ha hb
    | true =>
      simp only [d105729, d106423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105730 q = 1) (hb : d106424 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105730, d106424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105730, d106424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d105731 q = 1) (hb : d106425 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105731, d106425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105731, d106425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d105739 q = 1) (hb : d106434 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105739, d106434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15011 q ha hb
    | true =>
      simp only [d105739, d106434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14999 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d105702 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d105740 q = 1) (hb : d106435 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105740, d106435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d105740, d106435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d105702 q = 1) (hb : d106444 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105702, d106444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15007 q ha hb
    | true =>
      simp only [d105702, d106444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d105741 q = 1) (hb : d106445 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105741, d106445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d105741, d106445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d105742 q = 1) (hb : d106446 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105742, d106446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d105742, d106446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d105743 q = 1) (hb : d106447 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105743, d106447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d105743, d106447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d105744 q = 1) (hb : d106448 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105744, d106448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105744, d106448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d105745 q = 1) (hb : d106449 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105745, d106449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105745, d106449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro15013 (p : Pattern) (ha : d105710 p = 1) (hb : d106462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105696 q = 1) (hb : d106438 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105696, d106438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15006 q ha hb
    | true =>
      simp only [d105696, d106438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105697 q = 1) (hb : d106439 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105697, d106439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105697, d106439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105698 q = 1) (hb : d106440 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105698, d106440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105698, d106440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105699 q = 1) (hb : d106441 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105699, d106441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105699, d106441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105700 q = 1) (hb : d106442 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105700, d106442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105700, d106442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105710 q = 1) (hb : d106462 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105710, d106462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105710, d106462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15014 (p : Pattern) (ha : d105746 p = 1) (hb : d106450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105696 q = 1) (hb : d106390 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105696, d106390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14998 q ha hb
    | true =>
      simp only [d105696, d106390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105697 q = 1) (hb : d106391 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105697, d106391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105697, d106391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105698 q = 1) (hb : d106392 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105698, d106392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105698, d106392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105699 q = 1) (hb : d106393 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105699, d106393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105699, d106393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105720 q = 1) (hb : d106414 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105720, d106414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105720, d106414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105746 q = 1) (hb : d106450 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105746, d106450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105746, d106450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15015 (p : Pattern) (ha : d105751 p = 1) (hb : d106455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105696 q = 1) (hb : d106390 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105696, d106390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14998 q ha hb
    | true =>
      simp only [d105696, d106390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105697 q = 1) (hb : d106391 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105697, d106391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105697, d106391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105698 q = 1) (hb : d106392 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105698, d106392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105698, d106392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105726 q = 1) (hb : d106420 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105726, d106420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105726, d106420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105727 q = 1) (hb : d106421 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105727, d106421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105727, d106421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105751 q = 1) (hb : d106455 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105751, d106455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105751, d106455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15016 (p : Pattern) (ha : d105755 p = 1) (hb : d106459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105733 q = 1) (hb : d106428 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105733, d106428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15010 q ha hb
    | true =>
      simp only [d105733, d106428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105734 q = 1) (hb : d106429 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105734, d106429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105734, d106429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105696 q = 1) (hb : d106390 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105696, d106390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14998 q ha hb
    | true =>
      simp only [d105696, d106390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105697 q = 1) (hb : d106391 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105697, d106391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105697, d106391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105735 q = 1) (hb : d106430 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105735, d106430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105735, d106430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105736 q = 1) (hb : d106431 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105736, d106431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105736, d106431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d105737 q = 1) (hb : d106432 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105737, d106432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105737, d106432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d105755 q = 1) (hb : d106459 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105755, d106459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d105755, d106459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro15017 (p : Pattern) (ha : d105762 p = 1) (hb : d106468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105722 q = 1) (hb : d106416 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105722, d106416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15008 q ha hb
    | true =>
      simp only [d105722, d106416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105723 q = 1) (hb : d106417 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105723, d106417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105723, d106417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105724 q = 1) (hb : d106418 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105724, d106418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105724, d106418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105725 q = 1) (hb : d106419 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105725, d106419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105725, d106419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105729 q = 1) (hb : d106423 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105729, d106423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15009 q ha hb
    | true =>
      simp only [d105729, d106423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105730 q = 1) (hb : d106424 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105730, d106424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105730, d106424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d105731 q = 1) (hb : d106425 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105731, d106425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105731, d106425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d105739 q = 1) (hb : d106434 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105739, d106434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15011 q ha hb
    | true =>
      simp only [d105739, d106434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14999 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d105702 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d105740 q = 1) (hb : d106435 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105740, d106435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d105740, d106435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d105702 q = 1) (hb : d106444 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105702, d106444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15007 q ha hb
    | true =>
      simp only [d105702, d106444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d105741 q = 1) (hb : d106445 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105741, d106445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d105741, d106445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d105742 q = 1) (hb : d106446 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105742, d106446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d105742, d106446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d105743 q = 1) (hb : d106447 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105743, d106447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d105743, d106447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d105744 q = 1) (hb : d106448 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105744, d106448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105744, d106448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d105747 q = 1) (hb : d106451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105747, d106451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15014 q ha hb
    | true =>
      simp only [d105747, d106451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d105748 q = 1) (hb : d106452 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105748, d106452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105748, d106452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d105749 q = 1) (hb : d106453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105749, d106453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d105749, d106453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d105750 q = 1) (hb : d106454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105750, d106454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105750, d106454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d105752 q = 1) (hb : d106456 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105752, d106456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15015 q ha hb
    | true =>
      simp only [d105752, d106456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d105753 q = 1) (hb : d106457 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105753, d106457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105753, d106457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d105754 q = 1) (hb : d106458 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105754, d106458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d105754, d106458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d105756 q = 1) (hb : d106460 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105756, d106460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15016 q ha hb
    | true =>
      simp only [d105756, d106460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15001 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d105711 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d105757 q = 1) (hb : d106461 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105757, d106461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d105757, d106461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d105711 q = 1) (hb : d106463 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105711, d106463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15013 q ha hb
    | true =>
      simp only [d105711, d106463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d105758 q = 1) (hb : d106464 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105758, d106464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d105758, d106464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d105759 q = 1) (hb : d106465 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105759, d106465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d105759, d106465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d105760 q = 1) (hb : d106466 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105760, d106466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d105760, d106466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d105761 q = 1) (hb : d106467 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105761, d106467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d105761, d106467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d105762 q = 1) (hb : d106468 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105762, d106468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d105762, d106468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro15018 (p : Pattern) (ha : d105764 p = 1) (hb : d106470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105702 q = 1) (hb : d106396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105702, d106396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14999 q ha hb
    | true =>
      simp only [d105702, d106396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105703 q = 1) (hb : d106397 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105703, d106397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105703, d106397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105704 q = 1) (hb : d106398 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105704, d106398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105704, d106398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105705 q = 1) (hb : d106399 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105705, d106399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105705, d106399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105706 q = 1) (hb : d106400 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105706, d106400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105706, d106400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105764 q = 1) (hb : d106470 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105764, d106470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105764, d106470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15019 (p : Pattern) (ha : d105771 p = 1) (hb : d106477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105756 q = 1) (hb : d106460 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105756, d106460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15016 q ha hb
    | true =>
      simp only [d105756, d106460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15001 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105711 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d105757 q = 1) (hb : d106461 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105757, d106461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d105757, d106461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d105711 q = 1) (hb : d106463 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105711, d106463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15013 q ha hb
    | true =>
      simp only [d105711, d106463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105758 q = 1) (hb : d106464 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105758, d106464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105758, d106464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105759 q = 1) (hb : d106465 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105759, d106465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105759, d106465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d105769 q = 1) (hb : d106475 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105769, d106475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105769, d106475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d105770 q = 1) (hb : d106476 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105770, d106476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105770, d106476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d105771 q = 1) (hb : d106477 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105771, d106477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105771, d106477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro15020 (p : Pattern) (ha : d105777 p = 1) (hb : d106484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d982 q = 1) (hb : d52601 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
    | true =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
  have h3 (q : Pattern) (ha : d983 q = 1) (hb : d52602 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d984 q = 1) (hb : d52603 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6921 q = 1) (hb : d52603 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52603 q = 1) (hb : d106483 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d105777 q = 1) (hb : d106484 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105777, d106484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105777, d106484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15021 (p : Pattern) (ha : d105780 p = 1) (hb : d106488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d987 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
    | true =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q ha hb
  have h3 (q : Pattern) (ha : d988 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d989 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d995 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52608 q = 1) (hb : d106487 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d105780 q = 1) (hb : d106488 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105780, d106488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105780, d106488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15022 (p : Pattern) (ha : d105786 p = 1) (hb : d106494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105778 q = 1) (hb : d106485 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105778, d106485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15020 q ha hb
    | true =>
      simp only [d105778, d106485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105779 q = 1) (hb : d106486 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105779, d106486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105779, d106486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105781 q = 1) (hb : d106489 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105781, d106489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15021 q ha hb
    | true =>
      simp only [d105781, d106489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105782 q = 1) (hb : d106490 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105782, d106490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105782, d106490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105783 q = 1) (hb : d106491 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105783, d106491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105783, d106491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105784 q = 1) (hb : d106492 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105784, d106492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105784, d106492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d105785 q = 1) (hb : d106493 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105785, d106493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105785, d106493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d105786 q = 1) (hb : d106494 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105786, d106494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d105786, d106494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro15023 (p : Pattern) (ha : d105790 p = 1) (hb : d106498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105781 q = 1) (hb : d106489 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105781, d106489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15021 q ha hb
    | true =>
      simp only [d105781, d106489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105782 q = 1) (hb : d106490 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105782, d106490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105782, d106490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105787 q = 1) (hb : d106495 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105787, d106495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105787, d106495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105788 q = 1) (hb : d106496 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105788, d106496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105788, d106496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105789 q = 1) (hb : d106497 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105789, d106497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105789, d106497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105790 q = 1) (hb : d106498 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105790, d106498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105790, d106498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15024 (p : Pattern) (ha : d5500 p = 1) (hb : d52600 p = 1) : d0 p = 1 := by
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
  have h14 (q : Pattern) (ha : d5495 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15003 q ha hb
  have h15 (q : Pattern) (ha : d5451 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15003 q ha hb
    | true =>
      simp only [d5451, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5496 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5496, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5452 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5452, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5497 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5497, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5498 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5498, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d5499 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5499, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d5499, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d5500 q = 1) (hb : d52600 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5500, d52600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5500, d52600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro15025 (p : Pattern) (ha : d5501 p = 1) (hb : d52605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5495 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15003 q ha hb
  have h2 (q : Pattern) (ha : d5451 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15003 q ha hb
    | true =>
      simp only [d5451, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5496 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5496, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5452 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5452, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5497 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5497, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5498 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5498, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5499 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5499, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5499, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5501 q = 1) (hb : d52605 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5501, d52605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5501, d52605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15026 (p : Pattern) (ha : d105780 p = 1) (hb : d106502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5502 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5502, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15024 q ha hb
    | true =>
      simp only [d5502, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15025 q ha hb
  have h3 (q : Pattern) (ha : d5503 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5503, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5503, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5504 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5504, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5504, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5505 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52608 q = 1) (hb : d106501 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d105780 q = 1) (hb : d106502 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105780, d106502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105780, d106502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15027 (p : Pattern) (ha : d105790 p = 1) (hb : d106508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105781 q = 1) (hb : d106503 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105781, d106503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15026 q ha hb
    | true =>
      simp only [d105781, d106503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105782 q = 1) (hb : d106504 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105782, d106504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105782, d106504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105787 q = 1) (hb : d106505 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105787, d106505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105787, d106505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105788 q = 1) (hb : d106506 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105788, d106506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105788, d106506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105789 q = 1) (hb : d106507 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105789, d106507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105789, d106507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105790 q = 1) (hb : d106508 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105790, d106508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105790, d106508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15028 (p : Pattern) (ha : d105798 p = 1) (hb : d106514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105791 q = 1) (hb : d106499 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105791, d106499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15022 q ha hb
    | true =>
      simp only [d105791, d106499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15023 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105792 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d105793 q = 1) (hb : d106500 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105793, d106500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d105793, d106500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d105792 q = 1) (hb : d106509 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105792, d106509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15027 q ha hb
    | true =>
      simp only [d105792, d106509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105794 q = 1) (hb : d106510 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105794, d106510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105794, d106510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105795 q = 1) (hb : d106511 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105795, d106511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105795, d106511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d105796 q = 1) (hb : d106512 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105796, d106512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105796, d106512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d105797 q = 1) (hb : d106513 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105797, d106513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105797, d106513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d105798 q = 1) (hb : d106514 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105798, d106514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105798, d106514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro15029 (p : Pattern) (ha : d105804 p = 1) (hb : d106520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105708 q = 1) (hb : d106402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105708, d106402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105708, d106402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15000 q ha hb
  have h2 (q : Pattern) (ha : d105709 q = 1) (hb : d106403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105709, d106403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d105709, d106403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d105717 q = 1) (hb : d106411 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105717, d106411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15000 q ha hb
    | true =>
      simp only [d105717, d106411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15002 q ha hb
  have h4 (q : Pattern) (ha : d105718 q = 1) (hb : d106412 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105718, d106412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105718, d106412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105719 q = 1) (hb : d106413 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105719, d106413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105719, d106413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105763 q = 1) (hb : d106469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105763, d106469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15012 q ha hb
    | true =>
      simp only [d105763, d106469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15017 q ha hb
  have h7 (q : Pattern) (ha : d105765 q = 1) (hb : d106471 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105765, d106471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15018 q ha hb
    | true =>
      simp only [d105765, d106471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d105766 q = 1) (hb : d106472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105766, d106472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105766, d106472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d105767 q = 1) (hb : d106473 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105767, d106473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d105767, d106473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d105768 q = 1) (hb : d106474 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105768, d106474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105768, d106474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d105772 q = 1) (hb : d106478 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105772, d106478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105772, d106478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15019 q ha hb
  have h12 (q : Pattern) (ha : d105773 q = 1) (hb : d106479 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105773, d106479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d105773, d106479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d105774 q = 1) (hb : d106480 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105774, d106480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d105774, d106480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d105775 q = 1) (hb : d106481 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105775, d106481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d105775, d106481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d105776 q = 1) (hb : d106482 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105776, d106482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d105776, d106482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d105799 q = 1) (hb : d106515 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105799, d106515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105799, d106515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15028 q ha hb
  have h17 (q : Pattern) (ha : d105800 q = 1) (hb : d106516 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105800, d106516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d105800, d106516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d105801 q = 1) (hb : d106517 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105801, d106517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d105801, d106517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d105802 q = 1) (hb : d106518 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105802, d106518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d105802, d106518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d105803 q = 1) (hb : d106519 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105803, d106519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d105803, d106519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d105804 q = 1) (hb : d106520 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d105804, d106520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d105804, d106520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro15030 (p : Pattern) (ha : d105810 p = 1) (hb : d106526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105805 q = 1) (hb : d106521 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d105805, d106521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105805, d106521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15029 q ha hb
  have h2 (q : Pattern) (ha : d105806 q = 1) (hb : d106522 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d105806, d106522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105806, d106522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105807 q = 1) (hb : d106523 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d105807, d106523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105807, d106523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d105808 q = 1) (hb : d106524 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d105808, d106524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105808, d106524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105809 q = 1) (hb : d106525 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d105809, d106525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105809, d106525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105810 q = 1) (hb : d106526 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d105810, d106526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105810, d106526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15031 (p : Pattern) (ha : d105813 p = 1) (hb : d106530 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1142 q = 1) (hb : d52723 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
    | true =>
      simp only [d1142, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro155 q ha hb
  have h3 (q : Pattern) (ha : d1143 q = 1) (hb : d52724 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1143, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1144 q = 1) (hb : d52725 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1144, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1146 q = 1) (hb : d52725 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52725 q = 1) (hb : d106529 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d105813 q = 1) (hb : d106530 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105813, d106530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105813, d106530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15032 (p : Pattern) (ha : d105819 p = 1) (hb : d106536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105814 q = 1) (hb : d106531 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105814, d106531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15031 q ha hb
    | true =>
      simp only [d105814, d106531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105815 q = 1) (hb : d106532 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105815, d106532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105815, d106532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105816 q = 1) (hb : d106533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105816, d106533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105816, d106533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105817 q = 1) (hb : d106534 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105817, d106534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105817, d106534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105818 q = 1) (hb : d106535 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105818, d106535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105818, d106535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105819 q = 1) (hb : d106536 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105819, d106536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105819, d106536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15033 (p : Pattern) (ha : d105825 p = 1) (hb : d106542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105820 q = 1) (hb : d106537 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105820, d106537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15032 q ha hb
    | true =>
      simp only [d105820, d106537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105821 q = 1) (hb : d106538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105821, d106538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105821, d106538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105822 q = 1) (hb : d106539 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105822, d106539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105822, d106539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105823 q = 1) (hb : d106540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105823, d106540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105823, d106540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105824 q = 1) (hb : d106541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105824, d106541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105824, d106541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105825 q = 1) (hb : d106542 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105825, d106542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105825, d106542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15034 (p : Pattern) (ha : d105828 p = 1) (hb : d106545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105814 q = 1) (hb : d106531 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105814, d106531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15031 q ha hb
    | true =>
      simp only [d105814, d106531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105815 q = 1) (hb : d106532 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105815, d106532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105815, d106532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105816 q = 1) (hb : d106533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105816, d106533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105816, d106533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105817 q = 1) (hb : d106534 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105817, d106534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105817, d106534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105818 q = 1) (hb : d106535 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105818, d106535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105818, d106535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105828 q = 1) (hb : d106545 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105828, d106545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105828, d106545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15035 (p : Pattern) (ha : d105834 p = 1) (hb : d106551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105820 q = 1) (hb : d106537 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105820, d106537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15032 q ha hb
    | true =>
      simp only [d105820, d106537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105821 q = 1) (hb : d106538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105821, d106538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105821, d106538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105822 q = 1) (hb : d106539 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105822, d106539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105822, d106539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105823 q = 1) (hb : d106540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105823, d106540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105823, d106540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105824 q = 1) (hb : d106541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105824, d106541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105824, d106541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105829 q = 1) (hb : d106546 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105829, d106546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15034 q ha hb
    | true =>
      simp only [d105829, d106546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d105830 q = 1) (hb : d106547 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105830, d106547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105830, d106547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d105831 q = 1) (hb : d106548 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105831, d106548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d105831, d106548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d105832 q = 1) (hb : d106549 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105832, d106549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105832, d106549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d105833 q = 1) (hb : d106550 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105833, d106550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105833, d106550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d105834 q = 1) (hb : d106551 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105834, d106551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105834, d106551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15036 (p : Pattern) (ha : d5539 p = 1) (hb : d52701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1094 q = 1) (hb : d52675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1095 q = 1) (hb : d52676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51870 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d133 q = 1) (hb : d52685 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d52685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d52685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d134 q = 1) (hb : d52686 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d52686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d134, d52686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5534 q = 1) (hb : d52687 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5534, d52687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5534, d52687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5535 q = 1) (hb : d52688 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5535, d52688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5535, d52688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5536 q = 1) (hb : d52689 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5536, d52689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5536, d52689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1115 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h11 (q : Pattern) (ha : d1116 q = 1) (hb : d52697 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, d52697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1116, d52697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d1117 q = 1) (hb : d52698 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1117, d52698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1117, d52698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d5537 q = 1) (hb : d52699 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5537, d52699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5537, d52699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5538 q = 1) (hb : d52700 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5538, d52700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5538, d52700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d5539 q = 1) (hb : d52701 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5539, d52701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5539, d52701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro15037 (p : Pattern) (ha : d5545 p = 1) (hb : d52709 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1112 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1113 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1122 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1123 q = 1) (hb : d52704 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1124 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1124, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1125 q = 1) (hb : d52706 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d52706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1125, d52706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5540 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5540, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15036 q ha hb
    | true =>
      simp only [d5540, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5541 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5541, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5541, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5542 q = 1) (hb : d52704 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5542, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5542, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5543 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5543, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5543, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d5544 q = 1) (hb : d52708 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5544, d52708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5544, d52708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d5545 q = 1) (hb : d52709 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5545, d52709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5545, d52709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro15038 (p : Pattern) (ha : d5546 p = 1) (hb : d52722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5540 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5540, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15036 q ha hb
    | true =>
      simp only [d5540, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5541 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5541, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5541, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5542 q = 1) (hb : d52704 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5542, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5542, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5543 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5543, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5543, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5544 q = 1) (hb : d52708 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5544, d52708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5544, d52708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52721 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5546 q = 1) (hb : d52722 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5546, d52722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5546, d52722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro15039 (p : Pattern) (ha : d105813 p = 1) (hb : d106578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5547 q = 1) (hb : d52723 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5547, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15037 q ha hb
    | true =>
      simp only [d5547, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15038 q ha hb
  have h3 (q : Pattern) (ha : d5548 q = 1) (hb : d52724 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5548, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5548, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5549 q = 1) (hb : d52725 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5549, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5549, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5550 q = 1) (hb : d52725 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52725 q = 1) (hb : d106577 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d105813 q = 1) (hb : d106578 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105813, d106578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105813, d106578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15040 (p : Pattern) (ha : d105819 p = 1) (hb : d106584 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105814 q = 1) (hb : d106579 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105814, d106579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15039 q ha hb
    | true =>
      simp only [d105814, d106579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105815 q = 1) (hb : d106580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105815, d106580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105815, d106580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105816 q = 1) (hb : d106581 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105816, d106581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105816, d106581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105817 q = 1) (hb : d106582 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105817, d106582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105817, d106582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105818 q = 1) (hb : d106583 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105818, d106583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105818, d106583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105819 q = 1) (hb : d106584 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105819, d106584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105819, d106584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15041 (p : Pattern) (ha : d105839 p = 1) (hb : d106556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105814 q = 1) (hb : d106531 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105814, d106531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15031 q ha hb
    | true =>
      simp only [d105814, d106531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105815 q = 1) (hb : d106532 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105815, d106532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105815, d106532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105816 q = 1) (hb : d106533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105816, d106533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105816, d106533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105817 q = 1) (hb : d106534 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105817, d106534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105817, d106534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105838 q = 1) (hb : d106555 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105838, d106555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105838, d106555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105839 q = 1) (hb : d106556 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105839, d106556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105839, d106556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15042 (p : Pattern) (ha : d105846 p = 1) (hb : d106563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105814 q = 1) (hb : d106531 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105814, d106531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15031 q ha hb
    | true =>
      simp only [d105814, d106531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105815 q = 1) (hb : d106532 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105815, d106532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105815, d106532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105816 q = 1) (hb : d106533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105816, d106533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105816, d106533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105844 q = 1) (hb : d106561 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105844, d106561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105844, d106561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105845 q = 1) (hb : d106562 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105845, d106562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105845, d106562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105846 q = 1) (hb : d106563 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105846, d106563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105846, d106563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15043 (p : Pattern) (ha : d105850 p = 1) (hb : d106568 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52712 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1129 q = 1) (hb : d52710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro152 q ha hb
    | true =>
      simp only [d1129, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
  have h3 (q : Pattern) (ha : d1130 q = 1) (hb : d52711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1130, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1131 q = 1) (hb : d52712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1131, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6954 q = 1) (hb : d52712 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52712 q = 1) (hb : d106567 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d105850 q = 1) (hb : d106568 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105850, d106568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105850, d106568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15044 (p : Pattern) (ha : d105856 p = 1) (hb : d106574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105851 q = 1) (hb : d106569 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105851, d106569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15043 q ha hb
    | true =>
      simp only [d105851, d106569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105852 q = 1) (hb : d106570 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105852, d106570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105852, d106570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105814 q = 1) (hb : d106531 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105814, d106531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15031 q ha hb
    | true =>
      simp only [d105814, d106531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105815 q = 1) (hb : d106532 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105815, d106532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105815, d106532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105853 q = 1) (hb : d106571 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105853, d106571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105853, d106571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105854 q = 1) (hb : d106572 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105854, d106572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105854, d106572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d105855 q = 1) (hb : d106573 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105855, d106573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105855, d106573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d105856 q = 1) (hb : d106574 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105856, d106574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105856, d106574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15045 (p : Pattern) (ha : d105863 p = 1) (hb : d106590 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105840 q = 1) (hb : d106557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105840, d106557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15041 q ha hb
    | true =>
      simp only [d105840, d106557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105841 q = 1) (hb : d106558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105841, d106558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105841, d106558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105842 q = 1) (hb : d106559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105842, d106559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105842, d106559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105843 q = 1) (hb : d106560 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105843, d106560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105843, d106560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105847 q = 1) (hb : d106564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105847, d106564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15042 q ha hb
    | true =>
      simp only [d105847, d106564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105848 q = 1) (hb : d106565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105848, d106565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105848, d106565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d105849 q = 1) (hb : d106566 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105849, d106566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105849, d106566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d105857 q = 1) (hb : d106575 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105857, d106575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15044 q ha hb
    | true =>
      simp only [d105857, d106575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15032 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d105820 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d105858 q = 1) (hb : d106576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105858, d106576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d105858, d106576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d105820 q = 1) (hb : d106585 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105820, d106585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15040 q ha hb
    | true =>
      simp only [d105820, d106585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d105859 q = 1) (hb : d106586 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105859, d106586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d105859, d106586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d105860 q = 1) (hb : d106587 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105860, d106587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d105860, d106587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d105861 q = 1) (hb : d106588 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105861, d106588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d105861, d106588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d105862 q = 1) (hb : d106589 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105862, d106589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105862, d106589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d105863 q = 1) (hb : d106590 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105863, d106590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105863, d106590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro15046 (p : Pattern) (ha : d105828 p = 1) (hb : d106603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105814 q = 1) (hb : d106579 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105814, d106579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15039 q ha hb
    | true =>
      simp only [d105814, d106579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105815 q = 1) (hb : d106580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105815, d106580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105815, d106580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105816 q = 1) (hb : d106581 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105816, d106581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105816, d106581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105817 q = 1) (hb : d106582 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105817, d106582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105817, d106582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105818 q = 1) (hb : d106583 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105818, d106583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105818, d106583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105828 q = 1) (hb : d106603 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105828, d106603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105828, d106603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15047 (p : Pattern) (ha : d105864 p = 1) (hb : d106591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105814 q = 1) (hb : d106531 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105814, d106531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15031 q ha hb
    | true =>
      simp only [d105814, d106531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105815 q = 1) (hb : d106532 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105815, d106532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105815, d106532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105816 q = 1) (hb : d106533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105816, d106533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105816, d106533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105817 q = 1) (hb : d106534 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105817, d106534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105817, d106534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105838 q = 1) (hb : d106555 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105838, d106555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105838, d106555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105864 q = 1) (hb : d106591 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105864, d106591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105864, d106591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15048 (p : Pattern) (ha : d105869 p = 1) (hb : d106596 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105814 q = 1) (hb : d106531 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105814, d106531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15031 q ha hb
    | true =>
      simp only [d105814, d106531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105815 q = 1) (hb : d106532 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105815, d106532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105815, d106532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105816 q = 1) (hb : d106533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105816, d106533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105816, d106533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105844 q = 1) (hb : d106561 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105844, d106561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105844, d106561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105845 q = 1) (hb : d106562 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105845, d106562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105845, d106562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105869 q = 1) (hb : d106596 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105869, d106596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105869, d106596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15049 (p : Pattern) (ha : d105873 p = 1) (hb : d106600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105851 q = 1) (hb : d106569 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105851, d106569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15043 q ha hb
    | true =>
      simp only [d105851, d106569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105852 q = 1) (hb : d106570 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105852, d106570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105852, d106570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105814 q = 1) (hb : d106531 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105814, d106531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15031 q ha hb
    | true =>
      simp only [d105814, d106531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105815 q = 1) (hb : d106532 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105815, d106532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105815, d106532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105853 q = 1) (hb : d106571 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105853, d106571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105853, d106571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105854 q = 1) (hb : d106572 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105854, d106572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105854, d106572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d105855 q = 1) (hb : d106573 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105855, d106573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105855, d106573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d105873 q = 1) (hb : d106600 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105873, d106600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d105873, d106600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro15050 (p : Pattern) (ha : d105880 p = 1) (hb : d106609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105840 q = 1) (hb : d106557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105840, d106557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15041 q ha hb
    | true =>
      simp only [d105840, d106557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105841 q = 1) (hb : d106558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105841, d106558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105841, d106558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105842 q = 1) (hb : d106559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105842, d106559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105842, d106559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105843 q = 1) (hb : d106560 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105843, d106560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105843, d106560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105847 q = 1) (hb : d106564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105847, d106564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15042 q ha hb
    | true =>
      simp only [d105847, d106564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105848 q = 1) (hb : d106565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105848, d106565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105848, d106565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d105849 q = 1) (hb : d106566 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105849, d106566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105849, d106566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d105857 q = 1) (hb : d106575 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105857, d106575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15044 q ha hb
    | true =>
      simp only [d105857, d106575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15032 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d105820 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d105858 q = 1) (hb : d106576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105858, d106576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d105858, d106576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d105820 q = 1) (hb : d106585 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105820, d106585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15040 q ha hb
    | true =>
      simp only [d105820, d106585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d105859 q = 1) (hb : d106586 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105859, d106586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d105859, d106586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d105860 q = 1) (hb : d106587 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105860, d106587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d105860, d106587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d105861 q = 1) (hb : d106588 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105861, d106588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d105861, d106588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d105862 q = 1) (hb : d106589 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105862, d106589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105862, d106589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d105865 q = 1) (hb : d106592 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105865, d106592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15047 q ha hb
    | true =>
      simp only [d105865, d106592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d105866 q = 1) (hb : d106593 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105866, d106593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105866, d106593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d105867 q = 1) (hb : d106594 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105867, d106594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d105867, d106594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d105868 q = 1) (hb : d106595 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105868, d106595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105868, d106595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d105870 q = 1) (hb : d106597 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105870, d106597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15048 q ha hb
    | true =>
      simp only [d105870, d106597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d105871 q = 1) (hb : d106598 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105871, d106598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105871, d106598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d105872 q = 1) (hb : d106599 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105872, d106599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d105872, d106599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d105874 q = 1) (hb : d106601 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105874, d106601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15049 q ha hb
    | true =>
      simp only [d105874, d106601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15034 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d105829 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d105875 q = 1) (hb : d106602 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105875, d106602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d105875, d106602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d105829 q = 1) (hb : d106604 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105829, d106604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15046 q ha hb
    | true =>
      simp only [d105829, d106604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d105876 q = 1) (hb : d106605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105876, d106605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d105876, d106605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d105877 q = 1) (hb : d106606 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105877, d106606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d105877, d106606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d105878 q = 1) (hb : d106607 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105878, d106607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d105878, d106607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d105879 q = 1) (hb : d106608 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105879, d106608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d105879, d106608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d105880 q = 1) (hb : d106609 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105880, d106609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d105880, d106609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro15051 (p : Pattern) (ha : d105882 p = 1) (hb : d106611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105820 q = 1) (hb : d106537 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105820, d106537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15032 q ha hb
    | true =>
      simp only [d105820, d106537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105821 q = 1) (hb : d106538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105821, d106538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105821, d106538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105822 q = 1) (hb : d106539 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105822, d106539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105822, d106539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105823 q = 1) (hb : d106540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105823, d106540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105823, d106540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105824 q = 1) (hb : d106541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105824, d106541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105824, d106541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105882 q = 1) (hb : d106611 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105882, d106611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105882, d106611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15052 (p : Pattern) (ha : d105889 p = 1) (hb : d106618 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105874 q = 1) (hb : d106601 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105874, d106601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15049 q ha hb
    | true =>
      simp only [d105874, d106601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15034 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105829 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d105875 q = 1) (hb : d106602 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105875, d106602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d105875, d106602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d105829 q = 1) (hb : d106604 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105829, d106604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15046 q ha hb
    | true =>
      simp only [d105829, d106604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105876 q = 1) (hb : d106605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105876, d106605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105876, d106605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105877 q = 1) (hb : d106606 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105877, d106606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105877, d106606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d105887 q = 1) (hb : d106616 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105887, d106616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105887, d106616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d105888 q = 1) (hb : d106617 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105888, d106617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105888, d106617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d105889 q = 1) (hb : d106618 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105889, d106618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105889, d106618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro15053 (p : Pattern) (ha : d105895 p = 1) (hb : d106625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52892 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1402 q = 1) (hb : d52890 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
    | true =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
  have h3 (q : Pattern) (ha : d1403 q = 1) (hb : d52891 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1404 q = 1) (hb : d52892 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7000 q = 1) (hb : d52892 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52892 q = 1) (hb : d106624 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d105895 q = 1) (hb : d106625 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105895, d106625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105895, d106625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15054 (p : Pattern) (ha : d105898 p = 1) (hb : d106629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1412 q = 1) (hb : d52900 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
    | true =>
      simp only [d1412, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro168 q ha hb
  have h3 (q : Pattern) (ha : d1413 q = 1) (hb : d52901 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1413, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1414 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1414, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1420 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52902 q = 1) (hb : d106628 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d105898 q = 1) (hb : d106629 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105898, d106629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105898, d106629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15055 (p : Pattern) (ha : d105904 p = 1) (hb : d106635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105896 q = 1) (hb : d106626 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105896, d106626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15053 q ha hb
    | true =>
      simp only [d105896, d106626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105897 q = 1) (hb : d106627 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105897, d106627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105897, d106627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105899 q = 1) (hb : d106630 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105899, d106630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15054 q ha hb
    | true =>
      simp only [d105899, d106630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105900 q = 1) (hb : d106631 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105900, d106631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105900, d106631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105901 q = 1) (hb : d106632 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105901, d106632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105901, d106632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105902 q = 1) (hb : d106633 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105902, d106633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105902, d106633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d105903 q = 1) (hb : d106634 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105903, d106634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105903, d106634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d105904 q = 1) (hb : d106635 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105904, d106635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d105904, d106635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro15056 (p : Pattern) (ha : d105908 p = 1) (hb : d106639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105899 q = 1) (hb : d106630 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105899, d106630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15054 q ha hb
    | true =>
      simp only [d105899, d106630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105900 q = 1) (hb : d106631 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105900, d106631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105900, d106631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105905 q = 1) (hb : d106636 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105905, d106636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105905, d106636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105906 q = 1) (hb : d106637 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105906, d106637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105906, d106637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105907 q = 1) (hb : d106638 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105907, d106638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105907, d106638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105908 q = 1) (hb : d106639 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105908, d106639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105908, d106639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15057 (p : Pattern) (ha : d5589 p = 1) (hb : d52889 p = 1) : d0 p = 1 := by
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
  have h14 (q : Pattern) (ha : d5584 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5584, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5584, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15036 q ha hb
  have h15 (q : Pattern) (ha : d5540 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5540, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15036 q ha hb
    | true =>
      simp only [d5540, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5585 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5585, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5585, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5541 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5541, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5541, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5586 q = 1) (hb : d52881 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5586, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5586, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5587 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5587, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5587, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d5588 q = 1) (hb : d52888 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5588, d52888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d5588, d52888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d5589 q = 1) (hb : d52889 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5589, d52889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5589, d52889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro15058 (p : Pattern) (ha : d5590 p = 1) (hb : d52899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5584 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5584, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5584, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15036 q ha hb
  have h2 (q : Pattern) (ha : d5540 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5540, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15036 q ha hb
    | true =>
      simp only [d5540, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5585 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5585, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5585, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5541 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5541, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5541, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5586 q = 1) (hb : d52881 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5586, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5586, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5587 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5587, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5587, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5588 q = 1) (hb : d52888 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5588, d52888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5588, d52888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52898 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d5590 q = 1) (hb : d52899 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5590, d52899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5590, d52899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro15059 (p : Pattern) (ha : d105898 p = 1) (hb : d106643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5591 q = 1) (hb : d52900 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5591, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15057 q ha hb
    | true =>
      simp only [d5591, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15058 q ha hb
  have h3 (q : Pattern) (ha : d5592 q = 1) (hb : d52901 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5592, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5592, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5593 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5593, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5593, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5594 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52902 q = 1) (hb : d106642 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d105898 q = 1) (hb : d106643 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105898, d106643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105898, d106643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15060 (p : Pattern) (ha : d105908 p = 1) (hb : d106649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105899 q = 1) (hb : d106644 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105899, d106644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15059 q ha hb
    | true =>
      simp only [d105899, d106644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105900 q = 1) (hb : d106645 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105900, d106645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105900, d106645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105905 q = 1) (hb : d106646 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105905, d106646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105905, d106646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105906 q = 1) (hb : d106647 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105906, d106647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105906, d106647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105907 q = 1) (hb : d106648 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105907, d106648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105907, d106648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105908 q = 1) (hb : d106649 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105908, d106649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105908, d106649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15061 (p : Pattern) (ha : d105916 p = 1) (hb : d106655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105909 q = 1) (hb : d106640 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105909, d106640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15055 q ha hb
    | true =>
      simp only [d105909, d106640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15056 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105910 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d105911 q = 1) (hb : d106641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105911, d106641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d105911, d106641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d105910 q = 1) (hb : d106650 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105910, d106650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15060 q ha hb
    | true =>
      simp only [d105910, d106650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105912 q = 1) (hb : d106651 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105912, d106651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105912, d106651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105913 q = 1) (hb : d106652 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105913, d106652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105913, d106652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d105914 q = 1) (hb : d106653 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105914, d106653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105914, d106653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d105915 q = 1) (hb : d106654 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105915, d106654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105915, d106654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d105916 q = 1) (hb : d106655 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105916, d106655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105916, d106655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro15062 (p : Pattern) (ha : d105922 p = 1) (hb : d106661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105826 q = 1) (hb : d106543 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105826, d106543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105826, d106543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15033 q ha hb
  have h2 (q : Pattern) (ha : d105827 q = 1) (hb : d106544 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105827, d106544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d105827, d106544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d105835 q = 1) (hb : d106552 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105835, d106552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15033 q ha hb
    | true =>
      simp only [d105835, d106552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15035 q ha hb
  have h4 (q : Pattern) (ha : d105836 q = 1) (hb : d106553 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105836, d106553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105836, d106553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105837 q = 1) (hb : d106554 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105837, d106554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105837, d106554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105881 q = 1) (hb : d106610 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105881, d106610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15045 q ha hb
    | true =>
      simp only [d105881, d106610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15050 q ha hb
  have h7 (q : Pattern) (ha : d105883 q = 1) (hb : d106612 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105883, d106612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15051 q ha hb
    | true =>
      simp only [d105883, d106612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d105884 q = 1) (hb : d106613 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105884, d106613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105884, d106613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d105885 q = 1) (hb : d106614 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105885, d106614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d105885, d106614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d105886 q = 1) (hb : d106615 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105886, d106615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105886, d106615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d105890 q = 1) (hb : d106619 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105890, d106619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105890, d106619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15052 q ha hb
  have h12 (q : Pattern) (ha : d105891 q = 1) (hb : d106620 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105891, d106620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d105891, d106620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d105892 q = 1) (hb : d106621 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105892, d106621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d105892, d106621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d105893 q = 1) (hb : d106622 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105893, d106622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d105893, d106622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d105894 q = 1) (hb : d106623 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105894, d106623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d105894, d106623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d105917 q = 1) (hb : d106656 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105917, d106656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105917, d106656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15061 q ha hb
  have h17 (q : Pattern) (ha : d105918 q = 1) (hb : d106657 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105918, d106657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d105918, d106657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d105919 q = 1) (hb : d106658 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105919, d106658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d105919, d106658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d105920 q = 1) (hb : d106659 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105920, d106659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d105920, d106659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d105921 q = 1) (hb : d106660 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105921, d106660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d105921, d106660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d105922 q = 1) (hb : d106661 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d105922, d106661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d105922, d106661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro15063 (p : Pattern) (ha : d105928 p = 1) (hb : d106667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105923 q = 1) (hb : d106662 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d105923, d106662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105923, d106662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15062 q ha hb
  have h2 (q : Pattern) (ha : d105924 q = 1) (hb : d106663 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d105924, d106663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105924, d106663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105925 q = 1) (hb : d106664 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d105925, d106664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105925, d106664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d105926 q = 1) (hb : d106665 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d105926, d106665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105926, d106665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105927 q = 1) (hb : d106666 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d105927, d106666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105927, d106666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105928 q = 1) (hb : d106667 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d105928, d106667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105928, d106667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15064 (p : Pattern) (ha : d105932 p = 1) (hb : d106672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1603 q = 1) (hb : d53044 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
    | true =>
      simp only [d1603, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro213 q ha hb
  have h3 (q : Pattern) (ha : d1604 q = 1) (hb : d53045 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1604, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1605 q = 1) (hb : d53046 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1605, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1607 q = 1) (hb : d53046 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53046 q = 1) (hb : d106671 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d105932 q = 1) (hb : d106672 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105932, d106672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105932, d106672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15065 (p : Pattern) (ha : d105938 p = 1) (hb : d106678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105933 q = 1) (hb : d106673 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105933, d106673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15064 q ha hb
    | true =>
      simp only [d105933, d106673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105934 q = 1) (hb : d106674 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105934, d106674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105934, d106674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105935 q = 1) (hb : d106675 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105935, d106675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105935, d106675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105936 q = 1) (hb : d106676 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105936, d106676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105936, d106676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105937 q = 1) (hb : d106677 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105937, d106677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105937, d106677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105938 q = 1) (hb : d106678 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105938, d106678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105938, d106678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15066 (p : Pattern) (ha : d105944 p = 1) (hb : d106684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105939 q = 1) (hb : d106679 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105939, d106679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15065 q ha hb
    | true =>
      simp only [d105939, d106679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105940 q = 1) (hb : d106680 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105940, d106680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105940, d106680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105941 q = 1) (hb : d106681 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105941, d106681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105941, d106681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105942 q = 1) (hb : d106682 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105942, d106682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105942, d106682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105943 q = 1) (hb : d106683 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105943, d106683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105943, d106683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105944 q = 1) (hb : d106684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105944, d106684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105944, d106684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15067 (p : Pattern) (ha : d105947 p = 1) (hb : d106687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105933 q = 1) (hb : d106673 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105933, d106673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15064 q ha hb
    | true =>
      simp only [d105933, d106673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105934 q = 1) (hb : d106674 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105934, d106674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105934, d106674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105935 q = 1) (hb : d106675 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105935, d106675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105935, d106675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105936 q = 1) (hb : d106676 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105936, d106676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105936, d106676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105937 q = 1) (hb : d106677 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105937, d106677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105937, d106677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105947 q = 1) (hb : d106687 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105947, d106687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105947, d106687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15068 (p : Pattern) (ha : d105953 p = 1) (hb : d106693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105939 q = 1) (hb : d106679 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105939, d106679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15065 q ha hb
    | true =>
      simp only [d105939, d106679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105940 q = 1) (hb : d106680 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105940, d106680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105940, d106680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105941 q = 1) (hb : d106681 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105941, d106681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105941, d106681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105942 q = 1) (hb : d106682 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105942, d106682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105942, d106682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105943 q = 1) (hb : d106683 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105943, d106683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105943, d106683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105948 q = 1) (hb : d106688 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105948, d106688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15067 q ha hb
    | true =>
      simp only [d105948, d106688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d105949 q = 1) (hb : d106689 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105949, d106689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105949, d106689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d105950 q = 1) (hb : d106690 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105950, d106690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d105950, d106690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d105951 q = 1) (hb : d106691 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105951, d106691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105951, d106691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d105952 q = 1) (hb : d106692 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105952, d106692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105952, d106692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d105953 q = 1) (hb : d106693 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105953, d106693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105953, d106693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15069 (p : Pattern) (ha : d1563 p = 1) (hb : d53000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d52107 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1519 q = 1) (hb : d52960 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51867 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1531 q = 1) (hb : d52981 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1531, d52981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1531, d52981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1547 q = 1) (hb : d52982 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1547, d52982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1547, d52982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1563 q = 1) (hb : d53000 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d1563, d53000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1563, d53000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro15070 (p : Pattern) (ha : d5629 p = 1) (hb : d53022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1543 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro203 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1544 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h3 (q : Pattern) (ha : d1545 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53000 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1549 q = 1) (hb : d53001 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1549, d53001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro204 q ha hb
    | true =>
      simp only [d1549, d53001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1550 q = 1) (hb : d53002 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1550, d53002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1550, d53002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5624 q = 1) (hb : d53003 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5624, d53003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5624, d53003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53007 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5625 q = 1) (hb : d53008 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5625, d53008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5625, d53008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5626 q = 1) (hb : d53009 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5626, d53009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5626, d53009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d5128 q = 1) (hb : d53016 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d53016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5128, d53016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15069 q ha hb
  have h13 (q : Pattern) (ha : d5129 q = 1) (hb : d53017 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, d53017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5129, d53017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d5130 q = 1) (hb : d53018 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5130, d53018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5130, d53018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d53019 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d5627 q = 1) (hb : d53020 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5627, d53020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5627, d53020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5628 q = 1) (hb : d53021 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5628, d53021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5628, d53021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d5629 q = 1) (hb : d53022 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5629, d53022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5629, d53022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro15071 (p : Pattern) (ha : d5635 p = 1) (hb : d53030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1571 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1572 q = 1) (hb : d53013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1573 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1573, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1583 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1584 q = 1) (hb : d53025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1585 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1585, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1586 q = 1) (hb : d53027 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1586, d53027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1586, d53027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5630 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5630, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15070 q ha hb
    | true =>
      simp only [d5630, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5631 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5631, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5631, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5632 q = 1) (hb : d53025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5632, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5632, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5633 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5633, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5633, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d5634 q = 1) (hb : d53029 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5634, d53029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5634, d53029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d5635 q = 1) (hb : d53030 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5635, d53030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5635, d53030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro15072 (p : Pattern) (ha : d5636 p = 1) (hb : d53043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5630 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5630, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15070 q ha hb
    | true =>
      simp only [d5630, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5631 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5631, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5631, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5632 q = 1) (hb : d53025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5632, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5632, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5633 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5633, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5633, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5634 q = 1) (hb : d53029 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5634, d53029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5634, d53029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53042 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5636 q = 1) (hb : d53043 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5636, d53043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5636, d53043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro15073 (p : Pattern) (ha : d105932 p = 1) (hb : d106720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5637 q = 1) (hb : d53044 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5637, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15071 q ha hb
    | true =>
      simp only [d5637, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15072 q ha hb
  have h3 (q : Pattern) (ha : d5638 q = 1) (hb : d53045 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5638, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5638, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5639 q = 1) (hb : d53046 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5639, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5639, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5640 q = 1) (hb : d53046 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53046 q = 1) (hb : d106719 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d105932 q = 1) (hb : d106720 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105932, d106720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105932, d106720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15074 (p : Pattern) (ha : d105938 p = 1) (hb : d106726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105933 q = 1) (hb : d106721 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105933, d106721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15073 q ha hb
    | true =>
      simp only [d105933, d106721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105934 q = 1) (hb : d106722 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105934, d106722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105934, d106722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105935 q = 1) (hb : d106723 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105935, d106723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105935, d106723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105936 q = 1) (hb : d106724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105936, d106724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105936, d106724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105937 q = 1) (hb : d106725 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105937, d106725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105937, d106725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105938 q = 1) (hb : d106726 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105938, d106726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105938, d106726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15075 (p : Pattern) (ha : d105958 p = 1) (hb : d106698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105933 q = 1) (hb : d106673 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105933, d106673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15064 q ha hb
    | true =>
      simp only [d105933, d106673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105934 q = 1) (hb : d106674 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105934, d106674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105934, d106674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105935 q = 1) (hb : d106675 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105935, d106675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105935, d106675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105936 q = 1) (hb : d106676 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105936, d106676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105936, d106676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105957 q = 1) (hb : d106697 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105957, d106697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105957, d106697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105958 q = 1) (hb : d106698 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105958, d106698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105958, d106698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15076 (p : Pattern) (ha : d105965 p = 1) (hb : d106705 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105933 q = 1) (hb : d106673 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105933, d106673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15064 q ha hb
    | true =>
      simp only [d105933, d106673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105934 q = 1) (hb : d106674 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105934, d106674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105934, d106674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105935 q = 1) (hb : d106675 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105935, d106675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105935, d106675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105963 q = 1) (hb : d106703 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105963, d106703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105963, d106703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105964 q = 1) (hb : d106704 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105964, d106704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105964, d106704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105965 q = 1) (hb : d106705 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105965, d106705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105965, d106705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15077 (p : Pattern) (ha : d105969 p = 1) (hb : d106710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1590 q = 1) (hb : d53031 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
    | true =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
  have h3 (q : Pattern) (ha : d1591 q = 1) (hb : d53032 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1592 q = 1) (hb : d53033 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7034 q = 1) (hb : d53033 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53033 q = 1) (hb : d106709 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d105969 q = 1) (hb : d106710 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105969, d106710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105969, d106710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15078 (p : Pattern) (ha : d105975 p = 1) (hb : d106716 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105970 q = 1) (hb : d106711 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105970, d106711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15077 q ha hb
    | true =>
      simp only [d105970, d106711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105971 q = 1) (hb : d106712 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105971, d106712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105971, d106712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105933 q = 1) (hb : d106673 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105933, d106673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15064 q ha hb
    | true =>
      simp only [d105933, d106673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105934 q = 1) (hb : d106674 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105934, d106674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105934, d106674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105972 q = 1) (hb : d106713 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105972, d106713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105972, d106713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105973 q = 1) (hb : d106714 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105973, d106714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105973, d106714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d105974 q = 1) (hb : d106715 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105974, d106715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105974, d106715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d105975 q = 1) (hb : d106716 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105975, d106716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105975, d106716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15079 (p : Pattern) (ha : d105982 p = 1) (hb : d106732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105959 q = 1) (hb : d106699 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105959, d106699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15075 q ha hb
    | true =>
      simp only [d105959, d106699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105960 q = 1) (hb : d106700 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105960, d106700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105960, d106700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105961 q = 1) (hb : d106701 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105961, d106701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105961, d106701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105962 q = 1) (hb : d106702 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105962, d106702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105962, d106702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105966 q = 1) (hb : d106706 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105966, d106706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15076 q ha hb
    | true =>
      simp only [d105966, d106706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105967 q = 1) (hb : d106707 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105967, d106707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105967, d106707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d105968 q = 1) (hb : d106708 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105968, d106708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105968, d106708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d105976 q = 1) (hb : d106717 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105976, d106717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15078 q ha hb
    | true =>
      simp only [d105976, d106717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15065 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d105939 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d105977 q = 1) (hb : d106718 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105977, d106718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d105977, d106718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d105939 q = 1) (hb : d106727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105939, d106727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15074 q ha hb
    | true =>
      simp only [d105939, d106727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d105978 q = 1) (hb : d106728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105978, d106728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d105978, d106728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d105979 q = 1) (hb : d106729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105979, d106729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d105979, d106729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d105980 q = 1) (hb : d106730 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105980, d106730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d105980, d106730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d105981 q = 1) (hb : d106731 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105981, d106731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105981, d106731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d105982 q = 1) (hb : d106732 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105982, d106732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105982, d106732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro15080 (p : Pattern) (ha : d105947 p = 1) (hb : d106745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105933 q = 1) (hb : d106721 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105933, d106721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15073 q ha hb
    | true =>
      simp only [d105933, d106721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105934 q = 1) (hb : d106722 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105934, d106722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105934, d106722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105935 q = 1) (hb : d106723 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105935, d106723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105935, d106723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105936 q = 1) (hb : d106724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105936, d106724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105936, d106724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105937 q = 1) (hb : d106725 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105937, d106725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105937, d106725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105947 q = 1) (hb : d106745 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105947, d106745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105947, d106745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15081 (p : Pattern) (ha : d105983 p = 1) (hb : d106733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105933 q = 1) (hb : d106673 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105933, d106673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15064 q ha hb
    | true =>
      simp only [d105933, d106673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105934 q = 1) (hb : d106674 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105934, d106674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105934, d106674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105935 q = 1) (hb : d106675 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105935, d106675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105935, d106675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105936 q = 1) (hb : d106676 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105936, d106676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105936, d106676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105957 q = 1) (hb : d106697 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105957, d106697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105957, d106697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105983 q = 1) (hb : d106733 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105983, d106733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105983, d106733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15082 (p : Pattern) (ha : d105988 p = 1) (hb : d106738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105933 q = 1) (hb : d106673 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105933, d106673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15064 q ha hb
    | true =>
      simp only [d105933, d106673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105934 q = 1) (hb : d106674 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105934, d106674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105934, d106674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105935 q = 1) (hb : d106675 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105935, d106675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105935, d106675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105963 q = 1) (hb : d106703 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105963, d106703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105963, d106703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105964 q = 1) (hb : d106704 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105964, d106704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105964, d106704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105988 q = 1) (hb : d106738 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105988, d106738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105988, d106738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15083 (p : Pattern) (ha : d105992 p = 1) (hb : d106742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105970 q = 1) (hb : d106711 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105970, d106711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15077 q ha hb
    | true =>
      simp only [d105970, d106711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105971 q = 1) (hb : d106712 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105971, d106712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105971, d106712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105933 q = 1) (hb : d106673 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105933, d106673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15064 q ha hb
    | true =>
      simp only [d105933, d106673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105934 q = 1) (hb : d106674 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105934, d106674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105934, d106674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105972 q = 1) (hb : d106713 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105972, d106713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105972, d106713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105973 q = 1) (hb : d106714 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105973, d106714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105973, d106714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d105974 q = 1) (hb : d106715 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105974, d106715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105974, d106715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d105992 q = 1) (hb : d106742 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105992, d106742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d105992, d106742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro15084 (p : Pattern) (ha : d105999 p = 1) (hb : d106751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105959 q = 1) (hb : d106699 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105959, d106699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15075 q ha hb
    | true =>
      simp only [d105959, d106699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105960 q = 1) (hb : d106700 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105960, d106700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105960, d106700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105961 q = 1) (hb : d106701 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105961, d106701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105961, d106701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105962 q = 1) (hb : d106702 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105962, d106702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105962, d106702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105966 q = 1) (hb : d106706 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105966, d106706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15076 q ha hb
    | true =>
      simp only [d105966, d106706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105967 q = 1) (hb : d106707 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105967, d106707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105967, d106707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d105968 q = 1) (hb : d106708 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105968, d106708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105968, d106708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d105976 q = 1) (hb : d106717 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105976, d106717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15078 q ha hb
    | true =>
      simp only [d105976, d106717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15065 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d105939 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d105977 q = 1) (hb : d106718 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105977, d106718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d105977, d106718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d105939 q = 1) (hb : d106727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105939, d106727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15074 q ha hb
    | true =>
      simp only [d105939, d106727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d105978 q = 1) (hb : d106728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105978, d106728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d105978, d106728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d105979 q = 1) (hb : d106729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105979, d106729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d105979, d106729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d105980 q = 1) (hb : d106730 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105980, d106730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d105980, d106730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d105981 q = 1) (hb : d106731 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105981, d106731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105981, d106731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d105984 q = 1) (hb : d106734 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105984, d106734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15081 q ha hb
    | true =>
      simp only [d105984, d106734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d105985 q = 1) (hb : d106735 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105985, d106735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105985, d106735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d105986 q = 1) (hb : d106736 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105986, d106736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d105986, d106736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d105987 q = 1) (hb : d106737 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105987, d106737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105987, d106737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d105989 q = 1) (hb : d106739 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105989, d106739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15082 q ha hb
    | true =>
      simp only [d105989, d106739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d105990 q = 1) (hb : d106740 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105990, d106740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105990, d106740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d105991 q = 1) (hb : d106741 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105991, d106741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d105991, d106741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d105993 q = 1) (hb : d106743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105993, d106743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15083 q ha hb
    | true =>
      simp only [d105993, d106743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15067 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d105948 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d105994 q = 1) (hb : d106744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105994, d106744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d105994, d106744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d105948 q = 1) (hb : d106746 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105948, d106746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15080 q ha hb
    | true =>
      simp only [d105948, d106746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d105995 q = 1) (hb : d106747 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105995, d106747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d105995, d106747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d105996 q = 1) (hb : d106748 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105996, d106748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d105996, d106748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d105997 q = 1) (hb : d106749 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105997, d106749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d105997, d106749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d105998 q = 1) (hb : d106750 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105998, d106750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d105998, d106750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d105999 q = 1) (hb : d106751 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105999, d106751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d105999, d106751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro15085 (p : Pattern) (ha : d106001 p = 1) (hb : d106753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105939 q = 1) (hb : d106679 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105939, d106679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15065 q ha hb
    | true =>
      simp only [d105939, d106679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d105940 q = 1) (hb : d106680 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105940, d106680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105940, d106680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105941 q = 1) (hb : d106681 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105941, d106681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105941, d106681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d105942 q = 1) (hb : d106682 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105942, d106682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105942, d106682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105943 q = 1) (hb : d106683 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105943, d106683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105943, d106683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d106001 q = 1) (hb : d106753 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106001, d106753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106001, d106753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15086 (p : Pattern) (ha : d106008 p = 1) (hb : d106760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105993 q = 1) (hb : d106743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105993, d106743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15083 q ha hb
    | true =>
      simp only [d105993, d106743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15067 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105948 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d105994 q = 1) (hb : d106744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105994, d106744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d105994, d106744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d105948 q = 1) (hb : d106746 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105948, d106746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15080 q ha hb
    | true =>
      simp only [d105948, d106746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105995 q = 1) (hb : d106747 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105995, d106747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d105995, d106747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d105996 q = 1) (hb : d106748 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105996, d106748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105996, d106748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106006 q = 1) (hb : d106758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106006, d106758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106006, d106758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d106007 q = 1) (hb : d106759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106007, d106759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106007, d106759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d106008 q = 1) (hb : d106760 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106008, d106760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106008, d106760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro15087 (p : Pattern) (ha : d106014 p = 1) (hb : d106767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53207 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1879 q = 1) (hb : d53205 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
    | true =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
  have h3 (q : Pattern) (ha : d1880 q = 1) (hb : d53206 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1881 q = 1) (hb : d53207 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7080 q = 1) (hb : d53207 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53207 q = 1) (hb : d106766 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d106014 q = 1) (hb : d106767 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d106014, d106767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d106014, d106767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15088 (p : Pattern) (ha : d106017 p = 1) (hb : d106771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1889 q = 1) (hb : d53215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
    | true =>
      simp only [d1889, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro226 q ha hb
  have h3 (q : Pattern) (ha : d1890 q = 1) (hb : d53216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1890, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1891 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1891, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1897 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53217 q = 1) (hb : d106770 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d106017 q = 1) (hb : d106771 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d106017, d106771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d106017, d106771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15089 (p : Pattern) (ha : d106023 p = 1) (hb : d106777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106015 q = 1) (hb : d106768 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d106015, d106768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15087 q ha hb
    | true =>
      simp only [d106015, d106768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106016 q = 1) (hb : d106769 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d106016, d106769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106016, d106769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106018 q = 1) (hb : d106772 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d106018, d106772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15088 q ha hb
    | true =>
      simp only [d106018, d106772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106019 q = 1) (hb : d106773 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d106019, d106773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106019, d106773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d106020 q = 1) (hb : d106774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d106020, d106774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106020, d106774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d106021 q = 1) (hb : d106775 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d106021, d106775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106021, d106775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d106022 q = 1) (hb : d106776 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d106022, d106776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d106022, d106776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d106023 q = 1) (hb : d106777 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d106023, d106777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d106023, d106777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro15090 (p : Pattern) (ha : d106027 p = 1) (hb : d106781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106018 q = 1) (hb : d106772 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d106018, d106772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15088 q ha hb
    | true =>
      simp only [d106018, d106772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106019 q = 1) (hb : d106773 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d106019, d106773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106019, d106773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106024 q = 1) (hb : d106778 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d106024, d106778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106024, d106778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106025 q = 1) (hb : d106779 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d106025, d106779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106025, d106779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106026 q = 1) (hb : d106780 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d106026, d106780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106026, d106780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106027 q = 1) (hb : d106781 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d106027, d106781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106027, d106781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15091 (p : Pattern) (ha : d5679 p = 1) (hb : d53204 p = 1) : d0 p = 1 := by
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
  have h14 (q : Pattern) (ha : d5674 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5674, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5674, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15070 q ha hb
  have h15 (q : Pattern) (ha : d5630 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5630, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15070 q ha hb
    | true =>
      simp only [d5630, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5675 q = 1) (hb : d53195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5675, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5675, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5631 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5631, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5631, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5676 q = 1) (hb : d53196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5676, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5676, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5677 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5677, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5677, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d5678 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5678, d53203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d5678, d53203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d5679 q = 1) (hb : d53204 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5679, d53204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5679, d53204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro15092 (p : Pattern) (ha : d5680 p = 1) (hb : d53214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5674 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5674, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5674, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15070 q ha hb
  have h2 (q : Pattern) (ha : d5630 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5630, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15070 q ha hb
    | true =>
      simp only [d5630, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5675 q = 1) (hb : d53195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5675, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5675, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5631 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5631, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5631, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5676 q = 1) (hb : d53196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5676, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5676, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5677 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5677, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5677, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5678 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5678, d53203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5678, d53203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53213 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d5680 q = 1) (hb : d53214 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5680, d53214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5680, d53214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro15093 (p : Pattern) (ha : d106017 p = 1) (hb : d106785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5681 q = 1) (hb : d53215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5681, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15091 q ha hb
    | true =>
      simp only [d5681, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15092 q ha hb
  have h3 (q : Pattern) (ha : d5682 q = 1) (hb : d53216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5682, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5682, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5683 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5683, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5683, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5684 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53217 q = 1) (hb : d106784 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d106017 q = 1) (hb : d106785 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d106017, d106785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d106017, d106785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15094 (p : Pattern) (ha : d106027 p = 1) (hb : d106791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106018 q = 1) (hb : d106786 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d106018, d106786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15093 q ha hb
    | true =>
      simp only [d106018, d106786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106019 q = 1) (hb : d106787 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d106019, d106787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106019, d106787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106024 q = 1) (hb : d106788 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d106024, d106788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106024, d106788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106025 q = 1) (hb : d106789 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d106025, d106789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106025, d106789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106026 q = 1) (hb : d106790 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d106026, d106790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106026, d106790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106027 q = 1) (hb : d106791 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d106027, d106791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106027, d106791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15095 (p : Pattern) (ha : d106035 p = 1) (hb : d106797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106028 q = 1) (hb : d106782 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106028, d106782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15089 q ha hb
    | true =>
      simp only [d106028, d106782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15090 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d106029 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d106030 q = 1) (hb : d106783 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106030, d106783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106030, d106783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d106029 q = 1) (hb : d106792 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106029, d106792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15094 q ha hb
    | true =>
      simp only [d106029, d106792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106031 q = 1) (hb : d106793 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106031, d106793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106031, d106793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106032 q = 1) (hb : d106794 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106032, d106794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106032, d106794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106033 q = 1) (hb : d106795 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106033, d106795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106033, d106795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d106034 q = 1) (hb : d106796 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106034, d106796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106034, d106796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d106035 q = 1) (hb : d106797 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106035, d106797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106035, d106797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro15096 (p : Pattern) (ha : d106041 p = 1) (hb : d106803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105945 q = 1) (hb : d106685 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105945, d106685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105945, d106685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15066 q ha hb
  have h2 (q : Pattern) (ha : d105946 q = 1) (hb : d106686 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105946, d106686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d105946, d106686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d105954 q = 1) (hb : d106694 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105954, d106694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15066 q ha hb
    | true =>
      simp only [d105954, d106694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15068 q ha hb
  have h4 (q : Pattern) (ha : d105955 q = 1) (hb : d106695 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105955, d106695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105955, d106695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105956 q = 1) (hb : d106696 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105956, d106696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d105956, d106696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d106000 q = 1) (hb : d106752 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d106000, d106752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15079 q ha hb
    | true =>
      simp only [d106000, d106752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15084 q ha hb
  have h7 (q : Pattern) (ha : d106002 q = 1) (hb : d106754 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d106002, d106754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15085 q ha hb
    | true =>
      simp only [d106002, d106754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d106003 q = 1) (hb : d106755 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106003, d106755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d106003, d106755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d106004 q = 1) (hb : d106756 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d106004, d106756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d106004, d106756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d106005 q = 1) (hb : d106757 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d106005, d106757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106005, d106757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d106009 q = 1) (hb : d106761 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d106009, d106761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106009, d106761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15086 q ha hb
  have h12 (q : Pattern) (ha : d106010 q = 1) (hb : d106762 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106010, d106762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d106010, d106762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d106011 q = 1) (hb : d106763 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d106011, d106763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d106011, d106763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d106012 q = 1) (hb : d106764 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d106012, d106764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d106012, d106764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d106013 q = 1) (hb : d106765 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d106013, d106765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d106013, d106765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d106036 q = 1) (hb : d106798 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d106036, d106798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106036, d106798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15095 q ha hb
  have h17 (q : Pattern) (ha : d106037 q = 1) (hb : d106799 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106037, d106799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d106037, d106799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d106038 q = 1) (hb : d106800 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d106038, d106800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d106038, d106800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d106039 q = 1) (hb : d106801 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d106039, d106801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d106039, d106801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d106040 q = 1) (hb : d106802 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d106040, d106802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d106040, d106802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d106041 q = 1) (hb : d106803 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d106041, d106803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d106041, d106803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro15097 (p : Pattern) (ha : d106047 p = 1) (hb : d106809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106042 q = 1) (hb : d106804 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d106042, d106804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106042, d106804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15096 q ha hb
  have h2 (q : Pattern) (ha : d106043 q = 1) (hb : d106805 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d106043, d106805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106043, d106805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106044 q = 1) (hb : d106806 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d106044, d106806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106044, d106806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d106045 q = 1) (hb : d106807 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d106045, d106807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106045, d106807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d106046 q = 1) (hb : d106808 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d106046, d106808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106046, d106808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d106047 q = 1) (hb : d106809 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d106047, d106809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106047, d106809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15098 (p : Pattern) (ha : d106052 p = 1) (hb : d106815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53367 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2086 q = 1) (hb : d53365 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
    | true =>
      simp only [d2086, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro272 q ha hb
  have h3 (q : Pattern) (ha : d2087 q = 1) (hb : d53366 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2087, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2088 q = 1) (hb : d53367 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2088, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2090 q = 1) (hb : d53367 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53367 q = 1) (hb : d106814 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d106052 q = 1) (hb : d106815 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d106052, d106815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d106052, d106815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15099 (p : Pattern) (ha : d106058 p = 1) (hb : d106821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106053 q = 1) (hb : d106816 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d106053, d106816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15098 q ha hb
    | true =>
      simp only [d106053, d106816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106054 q = 1) (hb : d106817 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d106054, d106817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106054, d106817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106055 q = 1) (hb : d106818 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d106055, d106818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106055, d106818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106056 q = 1) (hb : d106819 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d106056, d106819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106056, d106819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106057 q = 1) (hb : d106820 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d106057, d106820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106057, d106820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106058 q = 1) (hb : d106821 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d106058, d106821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106058, d106821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15100 (p : Pattern) (ha : d106064 p = 1) (hb : d106827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106059 q = 1) (hb : d106822 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106059, d106822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15099 q ha hb
    | true =>
      simp only [d106059, d106822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106060 q = 1) (hb : d106823 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106060, d106823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106060, d106823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106061 q = 1) (hb : d106824 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106061, d106824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106061, d106824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106062 q = 1) (hb : d106825 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106062, d106825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106062, d106825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d106063 q = 1) (hb : d106826 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106063, d106826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106063, d106826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d106064 q = 1) (hb : d106827 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106064, d106827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106064, d106827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15101 (p : Pattern) (ha : d106067 p = 1) (hb : d106830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106053 q = 1) (hb : d106816 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d106053, d106816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15098 q ha hb
    | true =>
      simp only [d106053, d106816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106054 q = 1) (hb : d106817 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d106054, d106817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106054, d106817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106055 q = 1) (hb : d106818 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d106055, d106818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106055, d106818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106056 q = 1) (hb : d106819 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d106056, d106819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106056, d106819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106057 q = 1) (hb : d106820 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d106057, d106820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106057, d106820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106067 q = 1) (hb : d106830 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d106067, d106830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106067, d106830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15102 (p : Pattern) (ha : d106073 p = 1) (hb : d106836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106059 q = 1) (hb : d106822 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106059, d106822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15099 q ha hb
    | true =>
      simp only [d106059, d106822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106060 q = 1) (hb : d106823 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106060, d106823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106060, d106823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106061 q = 1) (hb : d106824 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106061, d106824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106061, d106824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106062 q = 1) (hb : d106825 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106062, d106825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106062, d106825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d106063 q = 1) (hb : d106826 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106063, d106826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106063, d106826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d106068 q = 1) (hb : d106831 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106068, d106831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15101 q ha hb
    | true =>
      simp only [d106068, d106831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d106069 q = 1) (hb : d106832 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106069, d106832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106069, d106832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d106070 q = 1) (hb : d106833 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106070, d106833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d106070, d106833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d106071 q = 1) (hb : d106834 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106071, d106834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106071, d106834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d106072 q = 1) (hb : d106835 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106072, d106835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106072, d106835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d106073 q = 1) (hb : d106836 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106073, d106836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106073, d106836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15103 (p : Pattern) (ha : d2046 p = 1) (hb : d53319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d307 q = 1) (hb : d52106 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1997 q = 1) (hb : d53276 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53295 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2013 q = 1) (hb : d53296 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2013, d53296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2013, d53296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2027 q = 1) (hb : d53297 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2027, d53297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2027, d53297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2046 q = 1) (hb : d53319 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2046, d53319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2046, d53319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro15104 (p : Pattern) (ha : d5720 p = 1) (hb : d53343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d2020 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro259 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2024 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro260 q ha hb
  have h3 (q : Pattern) (ha : d2025 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5715 q = 1) (hb : d53324 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5715, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5715, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5716 q = 1) (hb : d53329 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5716, d53329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5716, d53329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5717 q = 1) (hb : d53330 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5717, d53330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5717, d53330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d5238 q = 1) (hb : d53337 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5238, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15103 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5239 q = 1) (hb : d53338 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5239, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d5243 q = 1) (hb : d53339 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5243, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5243, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d53340 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d5718 q = 1) (hb : d53341 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5718, d53341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5718, d53341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5719 q = 1) (hb : d53342 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5719, d53342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5719, d53342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d5720 q = 1) (hb : d53343 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5720, d53343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5720, d53343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro15105 (p : Pattern) (ha : d5726 p = 1) (hb : d53351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2054 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2055 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2056 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2066 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2067 q = 1) (hb : d53346 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2068 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2068, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2069 q = 1) (hb : d53348 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2069, d53348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2069, d53348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5721 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5721, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15104 q ha hb
    | true =>
      simp only [d5721, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5722 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5722, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5722, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5723 q = 1) (hb : d53346 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5723, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5723, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5724 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5724, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5724, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d5725 q = 1) (hb : d53350 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5725, d53350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5725, d53350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d5726 q = 1) (hb : d53351 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5726, d53351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5726, d53351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro15106 (p : Pattern) (ha : d5727 p = 1) (hb : d53364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5721 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5721, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15104 q ha hb
    | true =>
      simp only [d5721, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5722 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5722, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5722, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5723 q = 1) (hb : d53346 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5723, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5723, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5724 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5724, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5724, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5725 q = 1) (hb : d53350 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5725, d53350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5725, d53350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53363 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5727 q = 1) (hb : d53364 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5727, d53364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5727, d53364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro15107 (p : Pattern) (ha : d106052 p = 1) (hb : d106863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53367 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5728 q = 1) (hb : d53365 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5728, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15105 q ha hb
    | true =>
      simp only [d5728, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15106 q ha hb
  have h3 (q : Pattern) (ha : d5729 q = 1) (hb : d53366 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5729, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5729, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5730 q = 1) (hb : d53367 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5730, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5730, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5731 q = 1) (hb : d53367 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53367 q = 1) (hb : d106862 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d106052 q = 1) (hb : d106863 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d106052, d106863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d106052, d106863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15108 (p : Pattern) (ha : d106058 p = 1) (hb : d106869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106053 q = 1) (hb : d106864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d106053, d106864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15107 q ha hb
    | true =>
      simp only [d106053, d106864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106054 q = 1) (hb : d106865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d106054, d106865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106054, d106865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106055 q = 1) (hb : d106866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d106055, d106866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106055, d106866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106056 q = 1) (hb : d106867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d106056, d106867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106056, d106867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106057 q = 1) (hb : d106868 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d106057, d106868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106057, d106868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106058 q = 1) (hb : d106869 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d106058, d106869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106058, d106869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15109 (p : Pattern) (ha : d106078 p = 1) (hb : d106841 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106053 q = 1) (hb : d106816 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d106053, d106816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15098 q ha hb
    | true =>
      simp only [d106053, d106816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106054 q = 1) (hb : d106817 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d106054, d106817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106054, d106817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106055 q = 1) (hb : d106818 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d106055, d106818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106055, d106818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106056 q = 1) (hb : d106819 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d106056, d106819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106056, d106819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106077 q = 1) (hb : d106840 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d106077, d106840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106077, d106840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d106078 q = 1) (hb : d106841 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d106078, d106841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106078, d106841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15110 (p : Pattern) (ha : d106085 p = 1) (hb : d106848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106053 q = 1) (hb : d106816 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d106053, d106816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15098 q ha hb
    | true =>
      simp only [d106053, d106816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106054 q = 1) (hb : d106817 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d106054, d106817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106054, d106817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106055 q = 1) (hb : d106818 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d106055, d106818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106055, d106818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106083 q = 1) (hb : d106846 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d106083, d106846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106083, d106846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d106084 q = 1) (hb : d106847 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d106084, d106847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106084, d106847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106085 q = 1) (hb : d106848 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d106085, d106848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106085, d106848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15111 (p : Pattern) (ha : d106089 p = 1) (hb : d106853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53354 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2073 q = 1) (hb : d53352 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
    | true =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
  have h3 (q : Pattern) (ha : d2074 q = 1) (hb : d53353 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2075 q = 1) (hb : d53354 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7115 q = 1) (hb : d53354 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53354 q = 1) (hb : d106852 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d106089 q = 1) (hb : d106853 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d106089, d106853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d106089, d106853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15112 (p : Pattern) (ha : d106095 p = 1) (hb : d106859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106090 q = 1) (hb : d106854 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d106090, d106854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15111 q ha hb
    | true =>
      simp only [d106090, d106854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106091 q = 1) (hb : d106855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d106091, d106855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106091, d106855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106053 q = 1) (hb : d106816 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d106053, d106816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15098 q ha hb
    | true =>
      simp only [d106053, d106816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106054 q = 1) (hb : d106817 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d106054, d106817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106054, d106817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d106092 q = 1) (hb : d106856 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d106092, d106856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106092, d106856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d106093 q = 1) (hb : d106857 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d106093, d106857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106093, d106857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d106094 q = 1) (hb : d106858 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d106094, d106858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d106094, d106858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d106095 q = 1) (hb : d106859 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d106095, d106859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106095, d106859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15113 (p : Pattern) (ha : d106102 p = 1) (hb : d106875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106079 q = 1) (hb : d106842 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106079, d106842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15109 q ha hb
    | true =>
      simp only [d106079, d106842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106080 q = 1) (hb : d106843 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106080, d106843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106080, d106843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106081 q = 1) (hb : d106844 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106081, d106844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106081, d106844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106082 q = 1) (hb : d106845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106082, d106845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106082, d106845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d106086 q = 1) (hb : d106849 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106086, d106849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15110 q ha hb
    | true =>
      simp only [d106086, d106849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106087 q = 1) (hb : d106850 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106087, d106850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106087, d106850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106088 q = 1) (hb : d106851 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106088, d106851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d106088, d106851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d106096 q = 1) (hb : d106860 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106096, d106860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15112 q ha hb
    | true =>
      simp only [d106096, d106860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15099 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d106059 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d106097 q = 1) (hb : d106861 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106097, d106861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d106097, d106861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d106059 q = 1) (hb : d106870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106059, d106870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15108 q ha hb
    | true =>
      simp only [d106059, d106870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d106098 q = 1) (hb : d106871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106098, d106871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d106098, d106871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d106099 q = 1) (hb : d106872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106099, d106872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d106099, d106872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d106100 q = 1) (hb : d106873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106100, d106873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d106100, d106873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d106101 q = 1) (hb : d106874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106101, d106874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106101, d106874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d106102 q = 1) (hb : d106875 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106102, d106875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106102, d106875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro15114 (p : Pattern) (ha : d106067 p = 1) (hb : d106888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106053 q = 1) (hb : d106864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d106053, d106864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15107 q ha hb
    | true =>
      simp only [d106053, d106864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106054 q = 1) (hb : d106865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d106054, d106865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106054, d106865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106055 q = 1) (hb : d106866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d106055, d106866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106055, d106866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106056 q = 1) (hb : d106867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d106056, d106867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106056, d106867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106057 q = 1) (hb : d106868 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d106057, d106868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106057, d106868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106067 q = 1) (hb : d106888 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d106067, d106888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106067, d106888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15115 (p : Pattern) (ha : d106103 p = 1) (hb : d106876 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106053 q = 1) (hb : d106816 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d106053, d106816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15098 q ha hb
    | true =>
      simp only [d106053, d106816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106054 q = 1) (hb : d106817 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d106054, d106817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106054, d106817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106055 q = 1) (hb : d106818 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d106055, d106818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106055, d106818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106056 q = 1) (hb : d106819 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d106056, d106819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106056, d106819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106077 q = 1) (hb : d106840 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d106077, d106840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106077, d106840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d106103 q = 1) (hb : d106876 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d106103, d106876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106103, d106876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15116 (p : Pattern) (ha : d106108 p = 1) (hb : d106881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106053 q = 1) (hb : d106816 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d106053, d106816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15098 q ha hb
    | true =>
      simp only [d106053, d106816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106054 q = 1) (hb : d106817 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d106054, d106817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106054, d106817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106055 q = 1) (hb : d106818 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d106055, d106818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106055, d106818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106083 q = 1) (hb : d106846 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d106083, d106846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106083, d106846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d106084 q = 1) (hb : d106847 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d106084, d106847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106084, d106847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106108 q = 1) (hb : d106881 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d106108, d106881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106108, d106881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15117 (p : Pattern) (ha : d106112 p = 1) (hb : d106885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106090 q = 1) (hb : d106854 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d106090, d106854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15111 q ha hb
    | true =>
      simp only [d106090, d106854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106091 q = 1) (hb : d106855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d106091, d106855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106091, d106855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106053 q = 1) (hb : d106816 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d106053, d106816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15098 q ha hb
    | true =>
      simp only [d106053, d106816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106054 q = 1) (hb : d106817 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d106054, d106817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106054, d106817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d106092 q = 1) (hb : d106856 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d106092, d106856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106092, d106856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d106093 q = 1) (hb : d106857 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d106093, d106857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106093, d106857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d106094 q = 1) (hb : d106858 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d106094, d106858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d106094, d106858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d106112 q = 1) (hb : d106885 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d106112, d106885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d106112, d106885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro15118 (p : Pattern) (ha : d106119 p = 1) (hb : d106894 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106079 q = 1) (hb : d106842 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106079, d106842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15109 q ha hb
    | true =>
      simp only [d106079, d106842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106080 q = 1) (hb : d106843 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106080, d106843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106080, d106843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106081 q = 1) (hb : d106844 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106081, d106844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106081, d106844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106082 q = 1) (hb : d106845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106082, d106845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106082, d106845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d106086 q = 1) (hb : d106849 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106086, d106849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15110 q ha hb
    | true =>
      simp only [d106086, d106849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106087 q = 1) (hb : d106850 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106087, d106850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106087, d106850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106088 q = 1) (hb : d106851 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106088, d106851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d106088, d106851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d106096 q = 1) (hb : d106860 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106096, d106860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15112 q ha hb
    | true =>
      simp only [d106096, d106860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15099 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d106059 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d106097 q = 1) (hb : d106861 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106097, d106861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d106097, d106861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d106059 q = 1) (hb : d106870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106059, d106870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15108 q ha hb
    | true =>
      simp only [d106059, d106870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d106098 q = 1) (hb : d106871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106098, d106871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d106098, d106871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d106099 q = 1) (hb : d106872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106099, d106872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d106099, d106872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d106100 q = 1) (hb : d106873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106100, d106873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d106100, d106873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d106101 q = 1) (hb : d106874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106101, d106874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106101, d106874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d106104 q = 1) (hb : d106877 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106104, d106877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15115 q ha hb
    | true =>
      simp only [d106104, d106877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d106105 q = 1) (hb : d106878 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106105, d106878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106105, d106878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d106106 q = 1) (hb : d106879 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106106, d106879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d106106, d106879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d106107 q = 1) (hb : d106880 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106107, d106880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106107, d106880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d106109 q = 1) (hb : d106882 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106109, d106882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15116 q ha hb
    | true =>
      simp only [d106109, d106882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d106110 q = 1) (hb : d106883 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106110, d106883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106110, d106883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d106111 q = 1) (hb : d106884 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106111, d106884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d106111, d106884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d106113 q = 1) (hb : d106886 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106113, d106886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15117 q ha hb
    | true =>
      simp only [d106113, d106886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15101 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d106068 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d106114 q = 1) (hb : d106887 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106114, d106887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d106114, d106887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d106068 q = 1) (hb : d106889 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106068, d106889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15114 q ha hb
    | true =>
      simp only [d106068, d106889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d106115 q = 1) (hb : d106890 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106115, d106890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d106115, d106890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d106116 q = 1) (hb : d106891 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106116, d106891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d106116, d106891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d106117 q = 1) (hb : d106892 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106117, d106892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d106117, d106892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d106118 q = 1) (hb : d106893 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106118, d106893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d106118, d106893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d106119 q = 1) (hb : d106894 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106119, d106894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d106119, d106894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro15119 (p : Pattern) (ha : d106121 p = 1) (hb : d106896 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106059 q = 1) (hb : d106822 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106059, d106822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15099 q ha hb
    | true =>
      simp only [d106059, d106822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106060 q = 1) (hb : d106823 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106060, d106823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106060, d106823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106061 q = 1) (hb : d106824 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106061, d106824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106061, d106824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106062 q = 1) (hb : d106825 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106062, d106825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106062, d106825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d106063 q = 1) (hb : d106826 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106063, d106826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106063, d106826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d106121 q = 1) (hb : d106896 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106121, d106896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106121, d106896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15120 (p : Pattern) (ha : d106128 p = 1) (hb : d106903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106113 q = 1) (hb : d106886 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106113, d106886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15117 q ha hb
    | true =>
      simp only [d106113, d106886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15101 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d106068 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d106114 q = 1) (hb : d106887 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106114, d106887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106114, d106887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d106068 q = 1) (hb : d106889 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106068, d106889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15114 q ha hb
    | true =>
      simp only [d106068, d106889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106115 q = 1) (hb : d106890 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106115, d106890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106115, d106890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106116 q = 1) (hb : d106891 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106116, d106891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106116, d106891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106126 q = 1) (hb : d106901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106126, d106901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106126, d106901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d106127 q = 1) (hb : d106902 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106127, d106902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106127, d106902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d106128 q = 1) (hb : d106903 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106128, d106903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106128, d106903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro15121 (p : Pattern) (ha : d106134 p = 1) (hb : d106910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53524 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2357 q = 1) (hb : d53522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
    | true =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
  have h3 (q : Pattern) (ha : d2358 q = 1) (hb : d53523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2359 q = 1) (hb : d53524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7161 q = 1) (hb : d53524 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53524 q = 1) (hb : d106909 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d106134 q = 1) (hb : d106910 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d106134, d106910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d106134, d106910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15122 (p : Pattern) (ha : d106137 p = 1) (hb : d106914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2367 q = 1) (hb : d53532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
    | true =>
      simp only [d2367, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro285 q ha hb
  have h3 (q : Pattern) (ha : d2368 q = 1) (hb : d53533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2368, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2369 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2369, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2375 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53534 q = 1) (hb : d106913 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d106137 q = 1) (hb : d106914 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d106137, d106914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d106137, d106914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15123 (p : Pattern) (ha : d106143 p = 1) (hb : d106920 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106135 q = 1) (hb : d106911 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d106135, d106911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15121 q ha hb
    | true =>
      simp only [d106135, d106911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106136 q = 1) (hb : d106912 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d106136, d106912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106136, d106912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106138 q = 1) (hb : d106915 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d106138, d106915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15122 q ha hb
    | true =>
      simp only [d106138, d106915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106139 q = 1) (hb : d106916 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d106139, d106916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106139, d106916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d106140 q = 1) (hb : d106917 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d106140, d106917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106140, d106917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d106141 q = 1) (hb : d106918 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d106141, d106918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106141, d106918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d106142 q = 1) (hb : d106919 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d106142, d106919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d106142, d106919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d106143 q = 1) (hb : d106920 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d106143, d106920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d106143, d106920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro15124 (p : Pattern) (ha : d106147 p = 1) (hb : d106924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106138 q = 1) (hb : d106915 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d106138, d106915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15122 q ha hb
    | true =>
      simp only [d106138, d106915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106139 q = 1) (hb : d106916 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d106139, d106916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106139, d106916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106144 q = 1) (hb : d106921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d106144, d106921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106144, d106921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106145 q = 1) (hb : d106922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d106145, d106922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106145, d106922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106146 q = 1) (hb : d106923 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d106146, d106923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106146, d106923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106147 q = 1) (hb : d106924 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d106147, d106924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106147, d106924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15125 (p : Pattern) (ha : d5770 p = 1) (hb : d53521 p = 1) : d0 p = 1 := by
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
  have h14 (q : Pattern) (ha : d5765 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5765, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5765, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15104 q ha hb
  have h15 (q : Pattern) (ha : d5721 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5721, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15104 q ha hb
    | true =>
      simp only [d5721, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5766 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5766, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5766, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5722 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5722, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5722, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5767 q = 1) (hb : d53513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5767, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5767, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5768 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5768, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5768, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d5769 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5769, d53520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d5769, d53520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d5770 q = 1) (hb : d53521 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5770, d53521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5770, d53521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro15126 (p : Pattern) (ha : d5771 p = 1) (hb : d53531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5765 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5765, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5765, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15104 q ha hb
  have h2 (q : Pattern) (ha : d5721 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5721, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15104 q ha hb
    | true =>
      simp only [d5721, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5766 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5766, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5766, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5722 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5722, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5722, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5767 q = 1) (hb : d53513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5767, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5767, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5768 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5768, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5768, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5769 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5769, d53520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5769, d53520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53530 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d5771 q = 1) (hb : d53531 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5771, d53531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5771, d53531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro15127 (p : Pattern) (ha : d106137 p = 1) (hb : d106928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5772 q = 1) (hb : d53532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5772, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15125 q ha hb
    | true =>
      simp only [d5772, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15126 q ha hb
  have h3 (q : Pattern) (ha : d5773 q = 1) (hb : d53533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5773, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5773, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5774 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5774, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5774, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5775 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53534 q = 1) (hb : d106927 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d106927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d106137 q = 1) (hb : d106928 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d106137, d106928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d106137, d106928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro15128 (p : Pattern) (ha : d106147 p = 1) (hb : d106934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106138 q = 1) (hb : d106929 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d106138, d106929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15127 q ha hb
    | true =>
      simp only [d106138, d106929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106139 q = 1) (hb : d106930 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d106139, d106930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106139, d106930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106144 q = 1) (hb : d106931 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d106144, d106931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106144, d106931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106145 q = 1) (hb : d106932 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d106145, d106932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106145, d106932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106146 q = 1) (hb : d106933 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d106146, d106933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106146, d106933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106147 q = 1) (hb : d106934 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d106147, d106934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106147, d106934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15129 (p : Pattern) (ha : d106155 p = 1) (hb : d106940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106148 q = 1) (hb : d106925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106148, d106925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15123 q ha hb
    | true =>
      simp only [d106148, d106925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15124 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d106149 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d106150 q = 1) (hb : d106926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106150, d106926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106150, d106926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d106149 q = 1) (hb : d106935 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106149, d106935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15128 q ha hb
    | true =>
      simp only [d106149, d106935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106151 q = 1) (hb : d106936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106151, d106936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106151, d106936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106152 q = 1) (hb : d106937 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106152, d106937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106152, d106937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106153 q = 1) (hb : d106938 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106153, d106938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106153, d106938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d106154 q = 1) (hb : d106939 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106154, d106939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106154, d106939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d106155 q = 1) (hb : d106940 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106155, d106940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106155, d106940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro15130 (p : Pattern) (ha : d106161 p = 1) (hb : d106946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106065 q = 1) (hb : d106828 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d106065, d106828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106065, d106828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15100 q ha hb
  have h2 (q : Pattern) (ha : d106066 q = 1) (hb : d106829 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106066, d106829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106066, d106829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d106074 q = 1) (hb : d106837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d106074, d106837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15100 q ha hb
    | true =>
      simp only [d106074, d106837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15102 q ha hb
  have h4 (q : Pattern) (ha : d106075 q = 1) (hb : d106838 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106075, d106838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106075, d106838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106076 q = 1) (hb : d106839 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d106076, d106839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106076, d106839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d106120 q = 1) (hb : d106895 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d106120, d106895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15113 q ha hb
    | true =>
      simp only [d106120, d106895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15118 q ha hb
  have h7 (q : Pattern) (ha : d106122 q = 1) (hb : d106897 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d106122, d106897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15119 q ha hb
    | true =>
      simp only [d106122, d106897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d106123 q = 1) (hb : d106898 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106123, d106898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d106123, d106898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d106124 q = 1) (hb : d106899 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d106124, d106899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d106124, d106899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d106125 q = 1) (hb : d106900 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d106125, d106900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106125, d106900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d106129 q = 1) (hb : d106904 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d106129, d106904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106129, d106904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15120 q ha hb
  have h12 (q : Pattern) (ha : d106130 q = 1) (hb : d106905 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106130, d106905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d106130, d106905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d106131 q = 1) (hb : d106906 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d106131, d106906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d106131, d106906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d106132 q = 1) (hb : d106907 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d106132, d106907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d106132, d106907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d106133 q = 1) (hb : d106908 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d106133, d106908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d106133, d106908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d106156 q = 1) (hb : d106941 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d106156, d106941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106156, d106941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15129 q ha hb
  have h17 (q : Pattern) (ha : d106157 q = 1) (hb : d106942 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106157, d106942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d106157, d106942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d106158 q = 1) (hb : d106943 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d106158, d106943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d106158, d106943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d106159 q = 1) (hb : d106944 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d106159, d106944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d106159, d106944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d106160 q = 1) (hb : d106945 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d106160, d106945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d106160, d106945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d106161 q = 1) (hb : d106946 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d106161, d106946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d106161, d106946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro15131 (p : Pattern) (ha : d106167 p = 1) (hb : d106952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106162 q = 1) (hb : d106947 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d106162, d106947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106162, d106947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15130 q ha hb
  have h2 (q : Pattern) (ha : d106163 q = 1) (hb : d106948 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d106163, d106948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106163, d106948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106164 q = 1) (hb : d106949 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d106164, d106949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106164, d106949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d106165 q = 1) (hb : d106950 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d106165, d106950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106165, d106950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d106166 q = 1) (hb : d106951 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d106166, d106951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106166, d106951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d106167 q = 1) (hb : d106952 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d106167, d106952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106167, d106952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15132 (p : Pattern) (ha : d106173 p = 1) (hb : d106958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d105694 q = 1) (hb : d106387 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d105694, d106387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14976 q ha hb
    | true =>
      simp only [d105694, d106387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14997 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d105811 q = 1) (hb : d106527 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d105811, d106527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d105811, d106527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15030 q ha hb
  have h3 (q : Pattern) (ha : d105812 q = 1) (hb : d106528 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d105812, d106528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105812, d106528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d105929 q = 1) (hb : d106668 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d105929, d106668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d105929, d106668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15063 q ha hb
  have h5 (q : Pattern) (ha : d105930 q = 1) (hb : d106669 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d105930, d106669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d105930, d106669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105931 q = 1) (hb : d106670 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d105931, d106670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105931, d106670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106048 q = 1) (hb : d106810 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d106048, d106810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d106048, d106810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15097 q ha hb
  have h8 (q : Pattern) (ha : d106049 q = 1) (hb : d106811 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d106049, d106811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d106049, d106811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d106050 q = 1) (hb : d106812 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d106050, d106812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d106050, d106812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d106051 q = 1) (hb : d106813 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d106051, d106813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d106051, d106813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d106168 q = 1) (hb : d106953 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d106168, d106953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d106168, d106953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15131 q ha hb
  have h12 (q : Pattern) (ha : d106169 q = 1) (hb : d106954 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d106169, d106954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d106169, d106954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d106170 q = 1) (hb : d106955 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d106170, d106955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d106170, d106955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d106171 q = 1) (hb : d106956 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d106171, d106956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d106171, d106956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d106172 q = 1) (hb : d106957 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d106172, d106957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d106172, d106957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d106173 q = 1) (hb : d106958 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d106173, d106958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d106173, d106958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro15133 (p : Pattern) (ha : d106179 p = 1) (hb : d106964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106174 q = 1) (hb : d106959 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d106174, d106959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15132 q ha hb
    | true =>
      simp only [d106174, d106959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106175 q = 1) (hb : d106960 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d106175, d106960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106175, d106960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d106176 q = 1) (hb : d106961 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d106176, d106961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106176, d106961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106177 q = 1) (hb : d106962 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d106177, d106962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106177, d106962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106178 q = 1) (hb : d106963 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d106178, d106963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106178, d106963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106179 q = 1) (hb : d106964 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d106179, d106964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106179, d106964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15134 (p : Pattern) (ha : d106185 p = 1) (hb : d106970 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106180 q = 1) (hb : d106965 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d106180, d106965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15133 q ha hb
    | true =>
      simp only [d106180, d106965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106181 q = 1) (hb : d106966 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d106181, d106966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106181, d106966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d106182 q = 1) (hb : d106967 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d106182, d106967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106182, d106967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106183 q = 1) (hb : d106968 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d106183, d106968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106183, d106968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106184 q = 1) (hb : d106969 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d106184, d106969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106184, d106969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106185 q = 1) (hb : d106970 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d106185, d106970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106185, d106970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15135 (p : Pattern) (ha : d106191 p = 1) (hb : d106976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106186 q = 1) (hb : d106971 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d106186, d106971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15134 q ha hb
    | true =>
      simp only [d106186, d106971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106187 q = 1) (hb : d106972 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d106187, d106972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106187, d106972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d106188 q = 1) (hb : d106973 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d106188, d106973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106188, d106973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106189 q = 1) (hb : d106974 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d106189, d106974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106189, d106974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106190 q = 1) (hb : d106975 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d106190, d106975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106190, d106975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106191 q = 1) (hb : d106976 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d106191, d106976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106191, d106976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15136 (p : Pattern) (ha : d106197 p = 1) (hb : d106982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106192 q = 1) (hb : d106977 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d106192, d106977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15135 q ha hb
    | true =>
      simp only [d106192, d106977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106193 q = 1) (hb : d106978 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d106193, d106978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106193, d106978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d106194 q = 1) (hb : d106979 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d106194, d106979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106194, d106979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106195 q = 1) (hb : d106980 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d106195, d106980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106195, d106980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106196 q = 1) (hb : d106981 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d106196, d106981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106196, d106981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106197 q = 1) (hb : d106982 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d106197, d106982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106197, d106982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15137 (p : Pattern) (ha : d106203 p = 1) (hb : d106988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106198 q = 1) (hb : d106983 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d106198, d106983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15136 q ha hb
    | true =>
      simp only [d106198, d106983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106199 q = 1) (hb : d106984 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d106199, d106984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106199, d106984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d106200 q = 1) (hb : d106985 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d106200, d106985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106200, d106985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106201 q = 1) (hb : d106986 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d106201, d106986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106201, d106986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106202 q = 1) (hb : d106987 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d106202, d106987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106202, d106987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106203 q = 1) (hb : d106988 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d106203, d106988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106203, d106988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15138 (p : Pattern) (ha : d106209 p = 1) (hb : d106994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106204 q = 1) (hb : d106989 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d106204, d106989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15137 q ha hb
    | true =>
      simp only [d106204, d106989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106205 q = 1) (hb : d106990 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d106205, d106990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106205, d106990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d106206 q = 1) (hb : d106991 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d106206, d106991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106206, d106991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106207 q = 1) (hb : d106992 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d106207, d106992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106207, d106992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106208 q = 1) (hb : d106993 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d106208, d106993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106208, d106993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106209 q = 1) (hb : d106994 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d106209, d106994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106209, d106994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15139 (p : Pattern) (ha : d106215 p = 1) (hb : d107000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106210 q = 1) (hb : d106995 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d106210, d106995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15138 q ha hb
    | true =>
      simp only [d106210, d106995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106211 q = 1) (hb : d106996 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d106211, d106996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106211, d106996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d106212 q = 1) (hb : d106997 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d106212, d106997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106212, d106997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106213 q = 1) (hb : d106998 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d106213, d106998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106213, d106998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106214 q = 1) (hb : d106999 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d106214, d106999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106214, d106999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106215 q = 1) (hb : d107000 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d106215, d107000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106215, d107000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15140 (p : Pattern) (ha : d53647 p = 1) (hb : d104544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14703 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14704 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14723 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14724 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
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
theorem andIntro15141 (p : Pattern) (ha : d53655 p = 1) (hb : d104544 p = 1) : d89102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d204 q = 1) (hb : d104544 q = 1) : d88154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14707 q ha hb
    | true =>
      simp only [d204, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14696 q ha hb
  have h2 (q : Pattern) (ha : d287 q = 1) (hb : d104544 q = 1) : d88202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288 q = 1) (hb : d104544 q = 1) : d88203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d88203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288, d88203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d289 q = 1) (hb : d104544 q = 1) : d88204 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d88204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d88204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290 q = 1) (hb : d104544 q = 1) : d88205 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d88205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d88205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53655 q = 1) (hb : d104544 q = 1) : d89102 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d89102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d89102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15142 (p : Pattern) (ha : d53665 p = 1) (hb : d104544 p = 1) : d89112 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244 q = 1) (hb : d104544 q = 1) : d88178 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14710 q ha hb
    | true =>
      simp only [d244, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14700 q ha hb
  have h2 (q : Pattern) (ha : d53661 q = 1) (hb : d104544 q = 1) : d89108 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d89108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, d89108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53662 q = 1) (hb : d104544 q = 1) : d89109 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d89109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53662, d89109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53663 q = 1) (hb : d104544 q = 1) : d89110 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d89110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d89110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53664 q = 1) (hb : d104544 q = 1) : d89111 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d89111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d89111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53665 q = 1) (hb : d104544 q = 1) : d89112 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d89112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d89112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15143 (p : Pattern) (ha : d53671 p = 1) (hb : d104544 p = 1) : d89118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d104544 q = 1) : d88207 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d88207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14720 q ha hb
    | true =>
      simp only [d292, d88207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14721 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d104544 q = 1) : d88208 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d88208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d88208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d104544 q = 1) : d89100 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d89100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, d89100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d104544 q = 1) : d89101 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d89101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d89101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d104544 q = 1) : d89103 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d89103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, d89103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15141 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d104544 q = 1) : d89104 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d89104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, d89104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d104544 q = 1) : d89105 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d89105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, d89105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d104544 q = 1) : d89106 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d89106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, d89106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d104544 q = 1) : d89107 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d89107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, d89107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d104544 q = 1) : d89113 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d89113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, d89113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15142 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d104544 q = 1) : d89114 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d89114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, d89114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d104544 q = 1) : d89115 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d89115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, d89115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d104544 q = 1) : d89116 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d89116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, d89116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d104544 q = 1) : d89117 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d89117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, d89117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d104544 q = 1) : d89118 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d89118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, d89118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro15144 (p : Pattern) (ha : d53677 p = 1) (hb : d104544 p = 1) : d89124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15140 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53672 q = 1) (hb : d104544 q = 1) : d89119 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d89119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53672, d89119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15143 q ha hb
  have h7 (q : Pattern) (ha : d53673 q = 1) (hb : d104544 q = 1) : d89120 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d89120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53673, d89120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53674 q = 1) (hb : d104544 q = 1) : d89121 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d89121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53674, d89121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53675 q = 1) (hb : d104544 q = 1) : d89122 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d89122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53675, d89122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53676 q = 1) (hb : d104544 q = 1) : d89123 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d89123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53676, d89123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53677 q = 1) (hb : d104544 q = 1) : d89124 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d89124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53677, d89124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15145 (p : Pattern) (ha : d53680 p = 1) (hb : d104544 p = 1) : d107003 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d502 q = 1) (hb : d104544 q = 1) : d106288 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, d106288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14748 q ha hb
    | true =>
      simp only [d502, d106288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14749 q ha hb
  have h2 (q : Pattern) (ha : d503 q = 1) (hb : d104544 q = 1) : d106289 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d106289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d503, d106289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d504 q = 1) (hb : d104544 q = 1) : d106290 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d106290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d504, d106290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d505 q = 1) (hb : d104544 q = 1) : d106291 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d106291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, d106291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d506 q = 1) (hb : d104544 q = 1) : d106292 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d106292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, d106292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53680 q = 1) (hb : d104544 q = 1) : d107003 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53680, d107003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53680, d107003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15146 (p : Pattern) (ha : d53691 p = 1) (hb : d104544 p = 1) : d107013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53686 q = 1) (hb : d104544 q = 1) : d106369 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53686, d106369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14776 q ha hb
    | true =>
      simp only [d53686, d106369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14755 q ha hb
  have h2 (q : Pattern) (ha : d53687 q = 1) (hb : d104544 q = 1) : d107009 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53687, d107009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53687, d107009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53688 q = 1) (hb : d104544 q = 1) : d107010 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53688, d107010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53688, d107010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53689 q = 1) (hb : d104544 q = 1) : d107011 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53689, d107011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53689, d107011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53690 q = 1) (hb : d104544 q = 1) : d107012 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53690, d107012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53690, d107012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53691 q = 1) (hb : d104544 q = 1) : d107013 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53691, d107013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53691, d107013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15147 (p : Pattern) (ha : d53697 p = 1) (hb : d104544 p = 1) : d107019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d104544 q = 1) : d106294 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d106294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14747 q ha hb
    | true =>
      simp only [d508, d106294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14750 q ha hb
  have h2 (q : Pattern) (ha : d509 q = 1) (hb : d104544 q = 1) : d106295 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d106295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d106295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53678 q = 1) (hb : d104544 q = 1) : d107001 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d107001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53678, d107001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53679 q = 1) (hb : d104544 q = 1) : d107002 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d107002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d107002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53681 q = 1) (hb : d104544 q = 1) : d107004 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, d107004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53681, d107004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15145 q ha hb
  have h6 (q : Pattern) (ha : d53682 q = 1) (hb : d104544 q = 1) : d107005 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, d107005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53682, d107005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53683 q = 1) (hb : d104544 q = 1) : d107006 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, d107006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53683, d107006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53684 q = 1) (hb : d104544 q = 1) : d107007 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, d107007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53684, d107007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53685 q = 1) (hb : d104544 q = 1) : d107008 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, d107008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53685, d107008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53692 q = 1) (hb : d104544 q = 1) : d107014 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53692, d107014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53692, d107014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15146 q ha hb
  have h11 (q : Pattern) (ha : d53693 q = 1) (hb : d104544 q = 1) : d107015 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53693, d107015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53693, d107015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53694 q = 1) (hb : d104544 q = 1) : d107016 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53694, d107016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53694, d107016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53695 q = 1) (hb : d104544 q = 1) : d107017 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53695, d107017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53695, d107017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53696 q = 1) (hb : d104544 q = 1) : d107018 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, d107018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53696, d107018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53697 q = 1) (hb : d104544 q = 1) : d107019 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53697, d107019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53697, d107019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro15148 (p : Pattern) (ha : d53703 p = 1) (hb : d104544 p = 1) : d107025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d104544 q = 1) : d107020 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, d107020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, d107020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15147 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d104544 q = 1) : d107021 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, d107021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, d107021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d104544 q = 1) : d107022 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, d107022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, d107022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d104544 q = 1) : d107023 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, d107023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, d107023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d104544 q = 1) : d107024 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, d107024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, d107024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d104544 q = 1) : d107025 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53703, d107025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53703, d107025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15149 (p : Pattern) (ha : d53707 p = 1) (hb : d104544 p = 1) : d107029 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d794 q = 1) (hb : d104544 q = 1) : d106405 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d106405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14786 q ha hb
    | true =>
      simp only [d794, d106405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14787 q ha hb
  have h2 (q : Pattern) (ha : d795 q = 1) (hb : d104544 q = 1) : d106406 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d106406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d795, d106406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d796 q = 1) (hb : d104544 q = 1) : d106407 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d106407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d796, d106407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d797 q = 1) (hb : d104544 q = 1) : d106408 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d106408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, d106408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d798 q = 1) (hb : d104544 q = 1) : d106409 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d106409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, d106409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53707 q = 1) (hb : d104544 q = 1) : d107029 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53707, d107029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53707, d107029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15150 (p : Pattern) (ha : d53718 p = 1) (hb : d104544 p = 1) : d107040 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53713 q = 1) (hb : d104544 q = 1) : d107035 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53713, d107035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14815 q ha hb
    | true =>
      simp only [d53713, d107035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14793 q ha hb
  have h2 (q : Pattern) (ha : d53714 q = 1) (hb : d104544 q = 1) : d107036 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53714, d107036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53714, d107036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53715 q = 1) (hb : d104544 q = 1) : d107037 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53715, d107037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53715, d107037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53716 q = 1) (hb : d104544 q = 1) : d107038 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53716, d107038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53716, d107038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53717 q = 1) (hb : d104544 q = 1) : d107039 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53717, d107039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53717, d107039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53718 q = 1) (hb : d104544 q = 1) : d107040 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53718, d107040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53718, d107040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15151 (p : Pattern) (ha : d53724 p = 1) (hb : d104544 p = 1) : d107046 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d104544 q = 1) : d106411 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d106411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14785 q ha hb
    | true =>
      simp only [d800, d106411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14788 q ha hb
  have h2 (q : Pattern) (ha : d801 q = 1) (hb : d104544 q = 1) : d106412 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d106412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d106412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53705 q = 1) (hb : d104544 q = 1) : d107027 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d107027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53705, d107027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53706 q = 1) (hb : d104544 q = 1) : d107028 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d107028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d107028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53708 q = 1) (hb : d104544 q = 1) : d107030 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, d107030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53708, d107030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15149 q ha hb
  have h6 (q : Pattern) (ha : d53709 q = 1) (hb : d104544 q = 1) : d107031 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, d107031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53709, d107031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53710 q = 1) (hb : d104544 q = 1) : d107032 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, d107032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53710, d107032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53711 q = 1) (hb : d104544 q = 1) : d107033 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, d107033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53711, d107033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53712 q = 1) (hb : d104544 q = 1) : d107034 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, d107034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53712, d107034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53719 q = 1) (hb : d104544 q = 1) : d107041 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53719, d107041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53719, d107041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15150 q ha hb
  have h11 (q : Pattern) (ha : d53720 q = 1) (hb : d104544 q = 1) : d107042 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53720, d107042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53720, d107042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53721 q = 1) (hb : d104544 q = 1) : d107043 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53721, d107043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53721, d107043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53722 q = 1) (hb : d104544 q = 1) : d107044 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53722, d107044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53722, d107044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53723 q = 1) (hb : d104544 q = 1) : d107045 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, d107045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53723, d107045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53724 q = 1) (hb : d104544 q = 1) : d107046 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53724, d107046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53724, d107046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro15152 (p : Pattern) (ha : d53730 p = 1) (hb : d104544 p = 1) : d107052 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d104544 q = 1) : d107047 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, d107047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, d107047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15151 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d104544 q = 1) : d107048 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, d107048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, d107048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d104544 q = 1) : d107049 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, d107049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, d107049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d104544 q = 1) : d107050 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, d107050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, d107050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d104544 q = 1) : d107051 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, d107051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, d107051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d104544 q = 1) : d107052 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53730, d107052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53730, d107052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15153 (p : Pattern) (ha : d53735 p = 1) (hb : d104544 p = 1) : d107057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1173 q = 1) (hb : d104544 q = 1) : d106546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d106546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14826 q ha hb
    | true =>
      simp only [d1173, d106546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14827 q ha hb
  have h2 (q : Pattern) (ha : d1174 q = 1) (hb : d104544 q = 1) : d106547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d106547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1174, d106547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1175 q = 1) (hb : d104544 q = 1) : d106548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d106548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1175, d106548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1176 q = 1) (hb : d104544 q = 1) : d106549 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d106549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, d106549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1177 q = 1) (hb : d104544 q = 1) : d106550 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d106550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, d106550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53735 q = 1) (hb : d104544 q = 1) : d107057 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53735, d107057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53735, d107057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15154 (p : Pattern) (ha : d53746 p = 1) (hb : d104544 p = 1) : d107068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53741 q = 1) (hb : d104544 q = 1) : d107063 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53741, d107063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14855 q ha hb
    | true =>
      simp only [d53741, d107063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14833 q ha hb
  have h2 (q : Pattern) (ha : d53742 q = 1) (hb : d104544 q = 1) : d107064 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53742, d107064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53742, d107064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53743 q = 1) (hb : d104544 q = 1) : d107065 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53743, d107065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53743, d107065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53744 q = 1) (hb : d104544 q = 1) : d107066 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53744, d107066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53744, d107066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53745 q = 1) (hb : d104544 q = 1) : d107067 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53745, d107067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53745, d107067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53746 q = 1) (hb : d104544 q = 1) : d107068 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53746, d107068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53746, d107068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15155 (p : Pattern) (ha : d53752 p = 1) (hb : d104544 p = 1) : d107074 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d104544 q = 1) : d106552 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d106552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14825 q ha hb
    | true =>
      simp only [d1179, d106552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14828 q ha hb
  have h2 (q : Pattern) (ha : d1180 q = 1) (hb : d104544 q = 1) : d106553 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d106553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d106553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53733 q = 1) (hb : d104544 q = 1) : d107055 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d107055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53733, d107055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53734 q = 1) (hb : d104544 q = 1) : d107056 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d107056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d107056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53736 q = 1) (hb : d104544 q = 1) : d107058 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, d107058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53736, d107058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15153 q ha hb
  have h6 (q : Pattern) (ha : d53737 q = 1) (hb : d104544 q = 1) : d107059 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, d107059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53737, d107059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53738 q = 1) (hb : d104544 q = 1) : d107060 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, d107060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53738, d107060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53739 q = 1) (hb : d104544 q = 1) : d107061 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, d107061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53739, d107061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53740 q = 1) (hb : d104544 q = 1) : d107062 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, d107062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53740, d107062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53747 q = 1) (hb : d104544 q = 1) : d107069 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53747, d107069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53747, d107069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15154 q ha hb
  have h11 (q : Pattern) (ha : d53748 q = 1) (hb : d104544 q = 1) : d107070 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53748, d107070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53748, d107070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53749 q = 1) (hb : d104544 q = 1) : d107071 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53749, d107071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53749, d107071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53750 q = 1) (hb : d104544 q = 1) : d107072 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53750, d107072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53750, d107072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53751 q = 1) (hb : d104544 q = 1) : d107073 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, d107073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53751, d107073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53752 q = 1) (hb : d104544 q = 1) : d107074 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, d107074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53752, d107074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro15156 (p : Pattern) (ha : d53758 p = 1) (hb : d104544 p = 1) : d107080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d104544 q = 1) : d107075 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, d107075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, d107075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15155 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d104544 q = 1) : d107076 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, d107076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, d107076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d104544 q = 1) : d107077 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, d107077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, d107077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d104544 q = 1) : d107078 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, d107078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, d107078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d104544 q = 1) : d107079 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, d107079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, d107079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d104544 q = 1) : d107080 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, d107080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, d107080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15157 (p : Pattern) (ha : d53764 p = 1) (hb : d104544 p = 1) : d107086 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1634 q = 1) (hb : d104544 q = 1) : d106688 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d106688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14866 q ha hb
    | true =>
      simp only [d1634, d106688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14867 q ha hb
  have h2 (q : Pattern) (ha : d1635 q = 1) (hb : d104544 q = 1) : d106689 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d106689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1635, d106689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1636 q = 1) (hb : d104544 q = 1) : d106690 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d106690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1636, d106690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1637 q = 1) (hb : d104544 q = 1) : d106691 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d106691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, d106691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1638 q = 1) (hb : d104544 q = 1) : d106692 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d106692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, d106692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53764 q = 1) (hb : d104544 q = 1) : d107086 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53764, d107086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53764, d107086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15158 (p : Pattern) (ha : d53775 p = 1) (hb : d104544 p = 1) : d107097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53770 q = 1) (hb : d104544 q = 1) : d107092 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53770, d107092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14895 q ha hb
    | true =>
      simp only [d53770, d107092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14873 q ha hb
  have h2 (q : Pattern) (ha : d53771 q = 1) (hb : d104544 q = 1) : d107093 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53771, d107093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53771, d107093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53772 q = 1) (hb : d104544 q = 1) : d107094 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53772, d107094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53772, d107094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53773 q = 1) (hb : d104544 q = 1) : d107095 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53773, d107095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53773, d107095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53774 q = 1) (hb : d104544 q = 1) : d107096 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53774, d107096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53774, d107096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53775 q = 1) (hb : d104544 q = 1) : d107097 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53775, d107097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53775, d107097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15159 (p : Pattern) (ha : d53781 p = 1) (hb : d104544 p = 1) : d107103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d104544 q = 1) : d106694 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d106694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14865 q ha hb
    | true =>
      simp only [d1640, d106694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14868 q ha hb
  have h2 (q : Pattern) (ha : d1641 q = 1) (hb : d104544 q = 1) : d106695 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d106695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, d106695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53762 q = 1) (hb : d104544 q = 1) : d107084 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d107084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53762, d107084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53763 q = 1) (hb : d104544 q = 1) : d107085 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d107085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d107085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53765 q = 1) (hb : d104544 q = 1) : d107087 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, d107087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53765, d107087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15157 q ha hb
  have h6 (q : Pattern) (ha : d53766 q = 1) (hb : d104544 q = 1) : d107088 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, d107088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53766, d107088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53767 q = 1) (hb : d104544 q = 1) : d107089 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, d107089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53767, d107089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53768 q = 1) (hb : d104544 q = 1) : d107090 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, d107090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53768, d107090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53769 q = 1) (hb : d104544 q = 1) : d107091 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, d107091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53769, d107091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53776 q = 1) (hb : d104544 q = 1) : d107098 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53776, d107098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53776, d107098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15158 q ha hb
  have h11 (q : Pattern) (ha : d53777 q = 1) (hb : d104544 q = 1) : d107099 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53777, d107099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53777, d107099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53778 q = 1) (hb : d104544 q = 1) : d107100 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53778, d107100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53778, d107100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53779 q = 1) (hb : d104544 q = 1) : d107101 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53779, d107101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53779, d107101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53780 q = 1) (hb : d104544 q = 1) : d107102 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53780, d107102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53780, d107102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53781 q = 1) (hb : d104544 q = 1) : d107103 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53781, d107103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53781, d107103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro15160 (p : Pattern) (ha : d53787 p = 1) (hb : d104544 p = 1) : d107109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53782 q = 1) (hb : d104544 q = 1) : d107104 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53782, d107104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53782, d107104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15159 q ha hb
  have h2 (q : Pattern) (ha : d53783 q = 1) (hb : d104544 q = 1) : d107105 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53783, d107105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53783, d107105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53784 q = 1) (hb : d104544 q = 1) : d107106 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53784, d107106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53784, d107106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53785 q = 1) (hb : d104544 q = 1) : d107107 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53785, d107107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53785, d107107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53786 q = 1) (hb : d104544 q = 1) : d107108 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53786, d107108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53786, d107108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53787 q = 1) (hb : d104544 q = 1) : d107109 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53787, d107109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53787, d107109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15161 (p : Pattern) (ha : d53794 p = 1) (hb : d104544 p = 1) : d107116 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2117 q = 1) (hb : d104544 q = 1) : d106831 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d106831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14906 q ha hb
    | true =>
      simp only [d2117, d106831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14907 q ha hb
  have h2 (q : Pattern) (ha : d2118 q = 1) (hb : d104544 q = 1) : d106832 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d106832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2118, d106832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2119 q = 1) (hb : d104544 q = 1) : d106833 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d106833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2119, d106833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2120 q = 1) (hb : d104544 q = 1) : d106834 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d106834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, d106834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2121 q = 1) (hb : d104544 q = 1) : d106835 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d106835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, d106835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53794 q = 1) (hb : d104544 q = 1) : d107116 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53794, d107116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53794, d107116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15162 (p : Pattern) (ha : d53805 p = 1) (hb : d104544 p = 1) : d107127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53800 q = 1) (hb : d104544 q = 1) : d107122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53800, d107122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14935 q ha hb
    | true =>
      simp only [d53800, d107122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14913 q ha hb
  have h2 (q : Pattern) (ha : d53801 q = 1) (hb : d104544 q = 1) : d107123 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53801, d107123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53801, d107123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53802 q = 1) (hb : d104544 q = 1) : d107124 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53802, d107124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53802, d107124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53803 q = 1) (hb : d104544 q = 1) : d107125 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53803, d107125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53803, d107125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53804 q = 1) (hb : d104544 q = 1) : d107126 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53804, d107126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53804, d107126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53805 q = 1) (hb : d104544 q = 1) : d107127 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53805, d107127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53805, d107127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15163 (p : Pattern) (ha : d53811 p = 1) (hb : d104544 p = 1) : d107133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d104544 q = 1) : d106837 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d106837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14905 q ha hb
    | true =>
      simp only [d2123, d106837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14908 q ha hb
  have h2 (q : Pattern) (ha : d2124 q = 1) (hb : d104544 q = 1) : d106838 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d106838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, d106838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53792 q = 1) (hb : d104544 q = 1) : d107114 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d107114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53792, d107114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53793 q = 1) (hb : d104544 q = 1) : d107115 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d107115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d107115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53795 q = 1) (hb : d104544 q = 1) : d107117 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, d107117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53795, d107117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15161 q ha hb
  have h6 (q : Pattern) (ha : d53796 q = 1) (hb : d104544 q = 1) : d107118 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, d107118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53796, d107118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53797 q = 1) (hb : d104544 q = 1) : d107119 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, d107119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53797, d107119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53798 q = 1) (hb : d104544 q = 1) : d107120 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, d107120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53798, d107120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53799 q = 1) (hb : d104544 q = 1) : d107121 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, d107121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53799, d107121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53806 q = 1) (hb : d104544 q = 1) : d107128 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53806, d107128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53806, d107128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15162 q ha hb
  have h11 (q : Pattern) (ha : d53807 q = 1) (hb : d104544 q = 1) : d107129 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53807, d107129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53807, d107129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53808 q = 1) (hb : d104544 q = 1) : d107130 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53808, d107130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53808, d107130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53809 q = 1) (hb : d104544 q = 1) : d107131 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53809, d107131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53809, d107131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53810 q = 1) (hb : d104544 q = 1) : d107132 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53810, d107132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53810, d107132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53811 q = 1) (hb : d104544 q = 1) : d107133 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53811, d107133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53811, d107133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro15164 (p : Pattern) (ha : d53817 p = 1) (hb : d104544 p = 1) : d107139 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53812 q = 1) (hb : d104544 q = 1) : d107134 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53812, d107134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53812, d107134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15163 q ha hb
  have h2 (q : Pattern) (ha : d53813 q = 1) (hb : d104544 q = 1) : d107135 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53813, d107135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53813, d107135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53814 q = 1) (hb : d104544 q = 1) : d107136 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53814, d107136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53814, d107136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53815 q = 1) (hb : d104544 q = 1) : d107137 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53815, d107137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53815, d107137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53816 q = 1) (hb : d104544 q = 1) : d107138 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53816, d107138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53816, d107138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53817 q = 1) (hb : d104544 q = 1) : d107139 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53817, d107139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53817, d107139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15165 (p : Pattern) (ha : d53823 p = 1) (hb : d104544 p = 1) : d107145 p = 1 := by
  have h0 (q : Pattern) (ha : d53704 q = 1) (hb : d104544 q = 1) : d107026 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53704, d107026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15144 q ha hb
    | true =>
      simp only [d53704, d107026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15148 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53731 q = 1) (hb : d104544 q = 1) : d107053 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53731, d107053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53731, d107053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15152 q ha hb
  have h3 (q : Pattern) (ha : d53732 q = 1) (hb : d104544 q = 1) : d107054 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53732, d107054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53732, d107054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53759 q = 1) (hb : d104544 q = 1) : d107081 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53759, d107081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53759, d107081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15156 q ha hb
  have h5 (q : Pattern) (ha : d53760 q = 1) (hb : d104544 q = 1) : d107082 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53760, d107082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53760, d107082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53761 q = 1) (hb : d104544 q = 1) : d107083 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53761, d107083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53761, d107083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53788 q = 1) (hb : d104544 q = 1) : d107110 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53788, d107110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53788, d107110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15160 q ha hb
  have h8 (q : Pattern) (ha : d53789 q = 1) (hb : d104544 q = 1) : d107111 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53789, d107111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53789, d107111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53790 q = 1) (hb : d104544 q = 1) : d107112 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53790, d107112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53790, d107112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53791 q = 1) (hb : d104544 q = 1) : d107113 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53791, d107113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53791, d107113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53818 q = 1) (hb : d104544 q = 1) : d107140 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53818, d107140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53818, d107140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15164 q ha hb
  have h12 (q : Pattern) (ha : d53819 q = 1) (hb : d104544 q = 1) : d107141 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53819, d107141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53819, d107141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53820 q = 1) (hb : d104544 q = 1) : d107142 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53820, d107142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53820, d107142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53821 q = 1) (hb : d104544 q = 1) : d107143 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53821, d107143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53821, d107143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53822 q = 1) (hb : d104544 q = 1) : d107144 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53822, d107144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53822, d107144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53823 q = 1) (hb : d104544 q = 1) : d107145 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53823, d107145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53823, d107145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro15166 (p : Pattern) (ha : d53829 p = 1) (hb : d104544 p = 1) : d107151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53824 q = 1) (hb : d104544 q = 1) : d107146 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53824, d107146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15165 q ha hb
    | true =>
      simp only [d53824, d107146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53825 q = 1) (hb : d104544 q = 1) : d107147 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53825, d107147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53825, d107147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53826 q = 1) (hb : d104544 q = 1) : d107148 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53826, d107148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53826, d107148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53827 q = 1) (hb : d104544 q = 1) : d107149 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53827, d107149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53827, d107149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53828 q = 1) (hb : d104544 q = 1) : d107150 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53828, d107150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53828, d107150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53829 q = 1) (hb : d104544 q = 1) : d107151 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53829, d107151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53829, d107151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15167 (p : Pattern) (ha : d53835 p = 1) (hb : d104544 p = 1) : d107157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53830 q = 1) (hb : d104544 q = 1) : d107152 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53830, d107152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15166 q ha hb
    | true =>
      simp only [d53830, d107152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53831 q = 1) (hb : d104544 q = 1) : d107153 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53831, d107153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53831, d107153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53832 q = 1) (hb : d104544 q = 1) : d107154 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53832, d107154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53832, d107154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53833 q = 1) (hb : d104544 q = 1) : d107155 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53833, d107155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53833, d107155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53834 q = 1) (hb : d104544 q = 1) : d107156 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53834, d107156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53834, d107156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53835 q = 1) (hb : d104544 q = 1) : d107157 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53835, d107157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53835, d107157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15168 (p : Pattern) (ha : d53841 p = 1) (hb : d104544 p = 1) : d107163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53836 q = 1) (hb : d104544 q = 1) : d107158 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, d107158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15167 q ha hb
    | true =>
      simp only [d53836, d107158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53837 q = 1) (hb : d104544 q = 1) : d107159 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, d107159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53837, d107159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53838 q = 1) (hb : d104544 q = 1) : d107160 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, d107160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53838, d107160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53839 q = 1) (hb : d104544 q = 1) : d107161 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, d107161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53839, d107161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53840 q = 1) (hb : d104544 q = 1) : d107162 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, d107162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53840, d107162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53841 q = 1) (hb : d104544 q = 1) : d107163 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, d107163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53841, d107163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15169 (p : Pattern) (ha : d53847 p = 1) (hb : d104545 p = 1) : d107169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d104544 q = 1) : d107164 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, d107164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15168 q ha hb
    | true =>
      simp only [d53842, d107164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d104544 q = 1) : d107165 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, d107165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, d107165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53844 q = 1) (hb : d104544 q = 1) : d107166 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, d107166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, d107166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d104544 q = 1) : d107167 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, d107167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53845, d107167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53846 q = 1) (hb : d104545 q = 1) : d107168 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, d104545, d107168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, d104545, d107168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d104545 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53847 q = 1) (hb : d104545 q = 1) : d107169 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, d107169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53847, d107169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15170 (p : Pattern) (ha : d53853 p = 1) (hb : d104545 p = 1) : d107175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104545 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d104545 q = 1) : d107170 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, d107170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15169 q ha hb
    | true =>
      simp only [d53848, d107170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d104545 q = 1) : d107171 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, d107171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, d107171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d104545 q = 1) : d107172 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, d107172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, d107172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d104545 q = 1) : d107173 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, d107173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, d107173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d104545 q = 1) : d107174 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, d107174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, d107174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d104545 q = 1) : d107175 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, d107175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, d107175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15171 (p : Pattern) (ha : d53859 p = 1) (hb : d104545 p = 1) : d107181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104545 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d104545 q = 1) : d107176 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, d107176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15170 q ha hb
    | true =>
      simp only [d53854, d107176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d104545 q = 1) : d107177 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, d107177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, d107177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d104545 q = 1) : d107178 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, d107178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, d107178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d104545 q = 1) : d107179 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, d107179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, d107179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d104545 q = 1) : d107180 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, d107180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, d107180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d104545 q = 1) : d107181 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, d107181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53859, d107181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15172 (p : Pattern) (ha : d53865 p = 1) (hb : d104545 p = 1) : d107187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104545 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d104545 q = 1) : d107182 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, d107182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15171 q ha hb
    | true =>
      simp only [d53860, d107182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d104545 q = 1) : d107183 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, d107183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, d107183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d104545 q = 1) : d107184 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, d107184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, d107184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d104545 q = 1) : d107185 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, d107185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, d107185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d104545 q = 1) : d107186 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, d107186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, d107186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d104545 q = 1) : d107187 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, d107187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, d107187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15173 (p : Pattern) (ha : d88199 p = 1) (hb : d105528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105509 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105515 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d105523 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d88147 q = 1) (hb : d105442 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d88147, d105442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14950 q ha hb
    | true =>
      simp only [d88147, d105442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88195 q = 1) (hb : d105524 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88195, d105524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88195, d105524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d105443 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d88196 q = 1) (hb : d105525 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88196, d105525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88196, d105525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88197 q = 1) (hb : d105526 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88197, d105526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88197, d105526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88198 q = 1) (hb : d105527 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88198, d105527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88198, d105527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88199 q = 1) (hb : d105528 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88199, d105528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88199, d105528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro15174 (p : Pattern) (ha : d88206 p = 1) (hb : d105544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d105509 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105515 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105523 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d88147 q = 1) (hb : d105442 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d88147, d105442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14950 q ha hb
    | true =>
      simp only [d88147, d105442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88195 q = 1) (hb : d105524 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88195, d105524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88195, d105524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d105443 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d88196 q = 1) (hb : d105525 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88196, d105525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88196, d105525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88197 q = 1) (hb : d105526 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88197, d105526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88197, d105526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88198 q = 1) (hb : d105527 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88198, d105527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88198, d105527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d105533 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d105537 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d105539 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d88154 q = 1) (hb : d105449 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d88154, d105449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14952 q ha hb
    | true =>
      simp only [d88154, d105449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d88202 q = 1) (hb : d105540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88202, d105540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d88202, d105540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d105450 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d88203 q = 1) (hb : d105541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88203, d105541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d88203, d105541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d88204 q = 1) (hb : d105542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88204, d105542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d88204, d105542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d88205 q = 1) (hb : d105543 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88205, d105543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88205, d105543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d88206 q = 1) (hb : d105544 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88206, d105544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88206, d105544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro15175 (p : Pattern) (ha : d89102 p = 1) (hb : d105553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105539 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d88154 q = 1) (hb : d105449 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d88154, d105449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14952 q ha hb
    | true =>
      simp only [d88154, d105449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d88202 q = 1) (hb : d105540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88202, d105540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88202, d105540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d105450 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d88203 q = 1) (hb : d105541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88203, d105541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88203, d105541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88204 q = 1) (hb : d105551 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88204, d105551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88204, d105551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88205 q = 1) (hb : d105552 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88205, d105552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88205, d105552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d89102 q = 1) (hb : d105553 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89102, d105553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89102, d105553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15176 (p : Pattern) (ha : d89112 p = 1) (hb : d105571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105566 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d88178 q = 1) (hb : d105472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d88178, d105472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14956 q ha hb
    | true =>
      simp only [d88178, d105472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89108 q = 1) (hb : d105567 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89108, d105567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89108, d105567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d105473 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89109 q = 1) (hb : d105568 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89109, d105568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89109, d105568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89110 q = 1) (hb : d105569 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89110, d105569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89110, d105569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89111 q = 1) (hb : d105570 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89111, d105570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89111, d105570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d89112 q = 1) (hb : d105571 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89112, d105571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89112, d105571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15177 (p : Pattern) (ha : d89118 p = 1) (hb : d105577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d105503 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88207 q = 1) (hb : d105545 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88207, d105545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15173 q ha hb
    | true =>
      simp only [d88207, d105545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15174 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105547 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88208 q = 1) (hb : d105548 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88208, d105548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88208, d105548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89100 q = 1) (hb : d105549 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89100, d105549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89100, d105549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89101 q = 1) (hb : d105550 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89101, d105550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89101, d105550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89103 q = 1) (hb : d105554 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89103, d105554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89103, d105554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15175 q ha hb
  have h8 (q : Pattern) (ha : d89104 q = 1) (hb : d105555 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89104, d105555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d89104, d105555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d89105 q = 1) (hb : d105556 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89105, d105556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d89105, d105556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d89106 q = 1) (hb : d105557 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89106, d105557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d89106, d105557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d89107 q = 1) (hb : d105558 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89107, d105558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89107, d105558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d89113 q = 1) (hb : d105572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89113, d105572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89113, d105572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15176 q ha hb
  have h13 (q : Pattern) (ha : d89114 q = 1) (hb : d105573 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89114, d105573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d89114, d105573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d89115 q = 1) (hb : d105574 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89115, d105574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d89115, d105574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d89116 q = 1) (hb : d105575 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89116, d105575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d89116, d105575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d89117 q = 1) (hb : d105576 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89117, d105576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89117, d105576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d89118 q = 1) (hb : d105577 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89118, d105577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d89118, d105577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro15178 (p : Pattern) (ha : d89124 p = 1) (hb : d105583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d105488 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d89119 q = 1) (hb : d105578 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89119, d105578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89119, d105578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15177 q ha hb
  have h3 (q : Pattern) (ha : d89120 q = 1) (hb : d105579 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89120, d105579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89120, d105579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89121 q = 1) (hb : d105580 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89121, d105580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89121, d105580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d89122 q = 1) (hb : d105581 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89122, d105581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89122, d105581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89123 q = 1) (hb : d105582 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89123, d105582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89123, d105582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89124 q = 1) (hb : d105583 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d89124, d105583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89124, d105583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro15179 (p : Pattern) (ha : d105631 p = 1) (hb : d106284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105611 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105617 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d105625 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d105588 q = 1) (hb : d106279 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105588, d106279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14977 q ha hb
    | true =>
      simp only [d105588, d106279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105626 q = 1) (hb : d106280 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105626, d106280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d105626, d106280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d105627 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d105628 q = 1) (hb : d106281 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105628, d106281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105628, d106281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d105629 q = 1) (hb : d106282 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105629, d106282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d105629, d106282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d105630 q = 1) (hb : d106283 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105630, d106283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d105630, d106283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d105631 q = 1) (hb : d106284 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105631, d106284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105631, d106284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro15180 (p : Pattern) (ha : d105648 p = 1) (hb : d106293 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d105611 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105617 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105625 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d105588 q = 1) (hb : d106279 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105588, d106279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14977 q ha hb
    | true =>
      simp only [d105588, d106279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d105626 q = 1) (hb : d106280 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105626, d106280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d105626, d106280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d105627 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d105628 q = 1) (hb : d106281 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105628, d106281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105628, d106281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d105629 q = 1) (hb : d106282 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105629, d106282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d105629, d106282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d105630 q = 1) (hb : d106283 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105630, d106283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105630, d106283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d105636 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d105640 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d105642 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d105597 q = 1) (hb : d106288 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105597, d106288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14979 q ha hb
    | true =>
      simp only [d105597, d106288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d105643 q = 1) (hb : d106289 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105643, d106289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d105643, d106289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d105644 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d105645 q = 1) (hb : d106290 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105645, d106290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d105645, d106290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d105646 q = 1) (hb : d106291 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105646, d106291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d105646, d106291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d105647 q = 1) (hb : d106292 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105647, d106292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d105647, d106292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d105648 q = 1) (hb : d106293 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105648, d106293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d105648, d106293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro15181 (p : Pattern) (ha : d105657 p = 1) (hb : d107003 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105642 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d105597 q = 1) (hb : d106288 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105597, d106288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14979 q ha hb
    | true =>
      simp only [d105597, d106288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d105643 q = 1) (hb : d106289 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105643, d106289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d105643, d106289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d105644 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d105645 q = 1) (hb : d106290 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105645, d106290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105645, d106290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d105655 q = 1) (hb : d106291 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105655, d106291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105655, d106291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d105656 q = 1) (hb : d106292 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105656, d106292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105656, d106292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d105657 q = 1) (hb : d107003 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105657, d107003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105657, d107003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15182 (p : Pattern) (ha : d105681 p = 1) (hb : d107013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105674 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d105675 q = 1) (hb : d106369 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105675, d106369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14994 q ha hb
    | true =>
      simp only [d105675, d106369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d105676 q = 1) (hb : d107009 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105676, d107009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d105676, d107009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d105677 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d105678 q = 1) (hb : d107010 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105678, d107010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105678, d107010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d105679 q = 1) (hb : d107011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105679, d107011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105679, d107011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d105680 q = 1) (hb : d107012 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105680, d107012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105680, d107012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d105681 q = 1) (hb : d107013 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105681, d107013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105681, d107013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15183 (p : Pattern) (ha : d105687 p = 1) (hb : d107019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d105605 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105649 q = 1) (hb : d106294 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105649, d106294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15179 q ha hb
    | true =>
      simp only [d105649, d106294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15180 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105651 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d105652 q = 1) (hb : d106295 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105652, d106295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d105652, d106295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d105653 q = 1) (hb : d107001 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105653, d107001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105653, d107001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d105654 q = 1) (hb : d107002 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105654, d107002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105654, d107002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d105658 q = 1) (hb : d107004 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105658, d107004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d105658, d107004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15181 q ha hb
  have h8 (q : Pattern) (ha : d105659 q = 1) (hb : d107005 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105659, d107005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d105659, d107005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d105660 q = 1) (hb : d107006 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105660, d107006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d105660, d107006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d105661 q = 1) (hb : d107007 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105661, d107007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d105661, d107007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d105662 q = 1) (hb : d107008 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105662, d107008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105662, d107008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d105682 q = 1) (hb : d107014 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105682, d107014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d105682, d107014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15182 q ha hb
  have h13 (q : Pattern) (ha : d105683 q = 1) (hb : d107015 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105683, d107015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d105683, d107015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d105684 q = 1) (hb : d107016 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105684, d107016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d105684, d107016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d105685 q = 1) (hb : d107017 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105685, d107017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d105685, d107017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d105686 q = 1) (hb : d107018 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105686, d107018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d105686, d107018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d105687 q = 1) (hb : d107019 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d105687, d107019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d105687, d107019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro15184 (p : Pattern) (ha : d105693 p = 1) (hb : d107025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105688 q = 1) (hb : d107020 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d105688, d107020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105688, d107020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15183 q ha hb
  have h2 (q : Pattern) (ha : d105689 q = 1) (hb : d107021 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d105689, d107021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105689, d107021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105690 q = 1) (hb : d107022 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d105690, d107022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105690, d107022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d105691 q = 1) (hb : d107023 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d105691, d107023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105691, d107023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105692 q = 1) (hb : d107024 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d105692, d107024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105692, d107024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105693 q = 1) (hb : d107025 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d105693, d107025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105693, d107025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15185 (p : Pattern) (ha : d105745 p = 1) (hb : d106401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105725 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105731 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d105739 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d105702 q = 1) (hb : d106396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105702, d106396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14999 q ha hb
    | true =>
      simp only [d105702, d106396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105740 q = 1) (hb : d106397 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105740, d106397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d105740, d106397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d105741 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d105742 q = 1) (hb : d106398 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105742, d106398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105742, d106398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d105743 q = 1) (hb : d106399 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105743, d106399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d105743, d106399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d105744 q = 1) (hb : d106400 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105744, d106400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d105744, d106400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d105745 q = 1) (hb : d106401 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105745, d106401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105745, d106401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro15186 (p : Pattern) (ha : d105762 p = 1) (hb : d106410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d105725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105731 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105739 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d105702 q = 1) (hb : d106396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105702, d106396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14999 q ha hb
    | true =>
      simp only [d105702, d106396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d105740 q = 1) (hb : d106397 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105740, d106397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d105740, d106397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d105741 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d105742 q = 1) (hb : d106398 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105742, d106398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105742, d106398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d105743 q = 1) (hb : d106399 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105743, d106399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d105743, d106399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d105744 q = 1) (hb : d106400 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105744, d106400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105744, d106400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d105750 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d105754 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d105756 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d105711 q = 1) (hb : d106405 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105711, d106405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15001 q ha hb
    | true =>
      simp only [d105711, d106405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d105757 q = 1) (hb : d106406 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105757, d106406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d105757, d106406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d105758 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d105759 q = 1) (hb : d106407 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105759, d106407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d105759, d106407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d105760 q = 1) (hb : d106408 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105760, d106408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d105760, d106408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d105761 q = 1) (hb : d106409 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105761, d106409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d105761, d106409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d105762 q = 1) (hb : d106410 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105762, d106410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d105762, d106410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro15187 (p : Pattern) (ha : d105771 p = 1) (hb : d107029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105756 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d105711 q = 1) (hb : d106405 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105711, d106405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15001 q ha hb
    | true =>
      simp only [d105711, d106405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d105757 q = 1) (hb : d106406 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105757, d106406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d105757, d106406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d105758 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d105759 q = 1) (hb : d106407 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105759, d106407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105759, d106407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d105769 q = 1) (hb : d106408 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105769, d106408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105769, d106408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d105770 q = 1) (hb : d106409 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105770, d106409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105770, d106409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d105771 q = 1) (hb : d107029 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105771, d107029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105771, d107029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15188 (p : Pattern) (ha : d105798 p = 1) (hb : d107040 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105791 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d105792 q = 1) (hb : d107035 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105792, d107035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15023 q ha hb
    | true =>
      simp only [d105792, d107035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d105793 q = 1) (hb : d107036 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105793, d107036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d105793, d107036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d105794 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d105795 q = 1) (hb : d107037 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105795, d107037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105795, d107037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d105796 q = 1) (hb : d107038 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105796, d107038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105796, d107038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d105797 q = 1) (hb : d107039 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105797, d107039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105797, d107039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d105798 q = 1) (hb : d107040 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105798, d107040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105798, d107040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15189 (p : Pattern) (ha : d105804 p = 1) (hb : d107046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d105719 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105763 q = 1) (hb : d106411 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105763, d106411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15185 q ha hb
    | true =>
      simp only [d105763, d106411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15186 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105765 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d105766 q = 1) (hb : d106412 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105766, d106412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d105766, d106412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d105767 q = 1) (hb : d107027 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105767, d107027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105767, d107027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d105768 q = 1) (hb : d107028 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105768, d107028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105768, d107028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d105772 q = 1) (hb : d107030 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105772, d107030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d105772, d107030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15187 q ha hb
  have h8 (q : Pattern) (ha : d105773 q = 1) (hb : d107031 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105773, d107031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d105773, d107031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d105774 q = 1) (hb : d107032 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105774, d107032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d105774, d107032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d105775 q = 1) (hb : d107033 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105775, d107033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d105775, d107033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d105776 q = 1) (hb : d107034 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105776, d107034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105776, d107034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d105799 q = 1) (hb : d107041 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105799, d107041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d105799, d107041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15188 q ha hb
  have h13 (q : Pattern) (ha : d105800 q = 1) (hb : d107042 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105800, d107042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d105800, d107042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d105801 q = 1) (hb : d107043 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105801, d107043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d105801, d107043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d105802 q = 1) (hb : d107044 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105802, d107044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d105802, d107044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d105803 q = 1) (hb : d107045 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105803, d107045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d105803, d107045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d105804 q = 1) (hb : d107046 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d105804, d107046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d105804, d107046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro15190 (p : Pattern) (ha : d105810 p = 1) (hb : d107052 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105805 q = 1) (hb : d107047 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d105805, d107047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105805, d107047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15189 q ha hb
  have h2 (q : Pattern) (ha : d105806 q = 1) (hb : d107048 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d105806, d107048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105806, d107048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105807 q = 1) (hb : d107049 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d105807, d107049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105807, d107049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d105808 q = 1) (hb : d107050 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d105808, d107050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105808, d107050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105809 q = 1) (hb : d107051 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d105809, d107051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105809, d107051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105810 q = 1) (hb : d107052 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d105810, d107052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105810, d107052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15191 (p : Pattern) (ha : d105863 p = 1) (hb : d106542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105843 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105849 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d105857 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d105820 q = 1) (hb : d106537 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105820, d106537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15032 q ha hb
    | true =>
      simp only [d105820, d106537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105858 q = 1) (hb : d106538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105858, d106538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d105858, d106538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d105859 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d105860 q = 1) (hb : d106539 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105860, d106539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105860, d106539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d105861 q = 1) (hb : d106540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105861, d106540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d105861, d106540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d105862 q = 1) (hb : d106541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105862, d106541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d105862, d106541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d105863 q = 1) (hb : d106542 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105863, d106542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105863, d106542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro15192 (p : Pattern) (ha : d105880 p = 1) (hb : d106551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d105843 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105849 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105857 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d105820 q = 1) (hb : d106537 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105820, d106537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15032 q ha hb
    | true =>
      simp only [d105820, d106537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d105858 q = 1) (hb : d106538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105858, d106538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d105858, d106538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d105859 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d105860 q = 1) (hb : d106539 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105860, d106539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105860, d106539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d105861 q = 1) (hb : d106540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105861, d106540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d105861, d106540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d105862 q = 1) (hb : d106541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105862, d106541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105862, d106541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d105868 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d105872 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d105874 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d105829 q = 1) (hb : d106546 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105829, d106546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15034 q ha hb
    | true =>
      simp only [d105829, d106546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d105875 q = 1) (hb : d106547 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105875, d106547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d105875, d106547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d105876 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d105877 q = 1) (hb : d106548 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105877, d106548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d105877, d106548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d105878 q = 1) (hb : d106549 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105878, d106549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d105878, d106549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d105879 q = 1) (hb : d106550 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105879, d106550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d105879, d106550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d105880 q = 1) (hb : d106551 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105880, d106551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d105880, d106551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro15193 (p : Pattern) (ha : d105889 p = 1) (hb : d107057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105874 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d105829 q = 1) (hb : d106546 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105829, d106546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15034 q ha hb
    | true =>
      simp only [d105829, d106546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d105875 q = 1) (hb : d106547 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105875, d106547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d105875, d106547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d105876 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d105877 q = 1) (hb : d106548 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105877, d106548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105877, d106548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d105887 q = 1) (hb : d106549 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105887, d106549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105887, d106549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d105888 q = 1) (hb : d106550 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105888, d106550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105888, d106550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d105889 q = 1) (hb : d107057 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105889, d107057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105889, d107057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15194 (p : Pattern) (ha : d105916 p = 1) (hb : d107068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105909 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d105910 q = 1) (hb : d107063 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105910, d107063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15056 q ha hb
    | true =>
      simp only [d105910, d107063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d105911 q = 1) (hb : d107064 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105911, d107064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d105911, d107064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d105912 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d105913 q = 1) (hb : d107065 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105913, d107065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105913, d107065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d105914 q = 1) (hb : d107066 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105914, d107066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105914, d107066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d105915 q = 1) (hb : d107067 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105915, d107067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105915, d107067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d105916 q = 1) (hb : d107068 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105916, d107068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105916, d107068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15195 (p : Pattern) (ha : d105922 p = 1) (hb : d107074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d105837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105881 q = 1) (hb : d106552 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105881, d106552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15191 q ha hb
    | true =>
      simp only [d105881, d106552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15192 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105883 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d105884 q = 1) (hb : d106553 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105884, d106553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d105884, d106553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d105885 q = 1) (hb : d107055 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105885, d107055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105885, d107055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d105886 q = 1) (hb : d107056 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105886, d107056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105886, d107056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d105890 q = 1) (hb : d107058 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105890, d107058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d105890, d107058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15193 q ha hb
  have h8 (q : Pattern) (ha : d105891 q = 1) (hb : d107059 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105891, d107059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d105891, d107059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d105892 q = 1) (hb : d107060 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105892, d107060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d105892, d107060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d105893 q = 1) (hb : d107061 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105893, d107061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d105893, d107061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d105894 q = 1) (hb : d107062 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105894, d107062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d105894, d107062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d105917 q = 1) (hb : d107069 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105917, d107069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d105917, d107069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15194 q ha hb
  have h13 (q : Pattern) (ha : d105918 q = 1) (hb : d107070 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105918, d107070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d105918, d107070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d105919 q = 1) (hb : d107071 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105919, d107071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d105919, d107071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d105920 q = 1) (hb : d107072 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105920, d107072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d105920, d107072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d105921 q = 1) (hb : d107073 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105921, d107073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d105921, d107073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d105922 q = 1) (hb : d107074 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d105922, d107074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d105922, d107074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro15196 (p : Pattern) (ha : d105928 p = 1) (hb : d107080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105923 q = 1) (hb : d107075 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d105923, d107075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105923, d107075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15195 q ha hb
  have h2 (q : Pattern) (ha : d105924 q = 1) (hb : d107076 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d105924, d107076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105924, d107076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d105925 q = 1) (hb : d107077 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d105925, d107077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105925, d107077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d105926 q = 1) (hb : d107078 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d105926, d107078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105926, d107078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d105927 q = 1) (hb : d107079 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d105927, d107079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105927, d107079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105928 q = 1) (hb : d107080 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d105928, d107080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105928, d107080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15197 (p : Pattern) (ha : d105982 p = 1) (hb : d106684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105962 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105968 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d105976 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d105939 q = 1) (hb : d106679 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105939, d106679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15065 q ha hb
    | true =>
      simp only [d105939, d106679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d105977 q = 1) (hb : d106680 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105977, d106680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d105977, d106680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d105978 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d105979 q = 1) (hb : d106681 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105979, d106681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105979, d106681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d105980 q = 1) (hb : d106682 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105980, d106682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d105980, d106682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d105981 q = 1) (hb : d106683 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105981, d106683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d105981, d106683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d105982 q = 1) (hb : d106684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105982, d106684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105982, d106684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro15198 (p : Pattern) (ha : d105999 p = 1) (hb : d106693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d105962 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105968 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105976 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d105939 q = 1) (hb : d106679 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105939, d106679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15065 q ha hb
    | true =>
      simp only [d105939, d106679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d105977 q = 1) (hb : d106680 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105977, d106680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d105977, d106680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d105978 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d105979 q = 1) (hb : d106681 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105979, d106681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d105979, d106681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d105980 q = 1) (hb : d106682 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105980, d106682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d105980, d106682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d105981 q = 1) (hb : d106683 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105981, d106683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d105981, d106683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d105987 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d105991 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d105993 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d105948 q = 1) (hb : d106688 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105948, d106688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15067 q ha hb
    | true =>
      simp only [d105948, d106688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d105994 q = 1) (hb : d106689 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105994, d106689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d105994, d106689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d105995 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d105996 q = 1) (hb : d106690 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105996, d106690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d105996, d106690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d105997 q = 1) (hb : d106691 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105997, d106691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d105997, d106691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d105998 q = 1) (hb : d106692 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105998, d106692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d105998, d106692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d105999 q = 1) (hb : d106693 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105999, d106693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d105999, d106693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro15199 (p : Pattern) (ha : d106008 p = 1) (hb : d107086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105993 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d105948 q = 1) (hb : d106688 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105948, d106688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15067 q ha hb
    | true =>
      simp only [d105948, d106688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d105994 q = 1) (hb : d106689 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105994, d106689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d105994, d106689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d105995 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d105996 q = 1) (hb : d106690 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105996, d106690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105996, d106690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d106006 q = 1) (hb : d106691 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106006, d106691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106006, d106691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106007 q = 1) (hb : d106692 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106007, d106692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106007, d106692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d106008 q = 1) (hb : d107086 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106008, d107086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106008, d107086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15200 (p : Pattern) (ha : d106035 p = 1) (hb : d107097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d106028 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d106029 q = 1) (hb : d107092 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106029, d107092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15090 q ha hb
    | true =>
      simp only [d106029, d107092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d106030 q = 1) (hb : d107093 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106030, d107093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d106030, d107093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d106031 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d106032 q = 1) (hb : d107094 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106032, d107094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106032, d107094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d106033 q = 1) (hb : d107095 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106033, d107095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106033, d107095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106034 q = 1) (hb : d107096 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106034, d107096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106034, d107096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d106035 q = 1) (hb : d107097 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106035, d107097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106035, d107097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15201 (p : Pattern) (ha : d106041 p = 1) (hb : d107103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d105956 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106000 q = 1) (hb : d106694 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d106000, d106694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15197 q ha hb
    | true =>
      simp only [d106000, d106694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15198 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d106002 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d106003 q = 1) (hb : d106695 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106003, d106695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106003, d106695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d106004 q = 1) (hb : d107084 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d106004, d107084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106004, d107084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d106005 q = 1) (hb : d107085 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d106005, d107085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106005, d107085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106009 q = 1) (hb : d107087 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d106009, d107087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d106009, d107087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15199 q ha hb
  have h8 (q : Pattern) (ha : d106010 q = 1) (hb : d107088 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106010, d107088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d106010, d107088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d106011 q = 1) (hb : d107089 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d106011, d107089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d106011, d107089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d106012 q = 1) (hb : d107090 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d106012, d107090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d106012, d107090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d106013 q = 1) (hb : d107091 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d106013, d107091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d106013, d107091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d106036 q = 1) (hb : d107098 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d106036, d107098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d106036, d107098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15200 q ha hb
  have h13 (q : Pattern) (ha : d106037 q = 1) (hb : d107099 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106037, d107099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d106037, d107099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d106038 q = 1) (hb : d107100 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d106038, d107100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d106038, d107100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d106039 q = 1) (hb : d107101 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d106039, d107101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d106039, d107101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d106040 q = 1) (hb : d107102 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d106040, d107102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d106040, d107102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d106041 q = 1) (hb : d107103 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d106041, d107103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d106041, d107103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro15202 (p : Pattern) (ha : d106047 p = 1) (hb : d107109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106042 q = 1) (hb : d107104 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d106042, d107104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106042, d107104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15201 q ha hb
  have h2 (q : Pattern) (ha : d106043 q = 1) (hb : d107105 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d106043, d107105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106043, d107105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106044 q = 1) (hb : d107106 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d106044, d107106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106044, d107106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d106045 q = 1) (hb : d107107 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d106045, d107107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106045, d107107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d106046 q = 1) (hb : d107108 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d106046, d107108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106046, d107108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d106047 q = 1) (hb : d107109 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d106047, d107109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106047, d107109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15203 (p : Pattern) (ha : d106102 p = 1) (hb : d106827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d106082 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d106088 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d106096 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d106059 q = 1) (hb : d106822 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106059, d106822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15099 q ha hb
    | true =>
      simp only [d106059, d106822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106097 q = 1) (hb : d106823 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106097, d106823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d106097, d106823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d106098 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d106099 q = 1) (hb : d106824 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106099, d106824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106099, d106824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d106100 q = 1) (hb : d106825 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106100, d106825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d106100, d106825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d106101 q = 1) (hb : d106826 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106101, d106826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d106101, d106826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d106102 q = 1) (hb : d106827 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106102, d106827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106102, d106827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro15204 (p : Pattern) (ha : d106119 p = 1) (hb : d106836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d106082 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d106088 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d106096 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d106059 q = 1) (hb : d106822 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106059, d106822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15099 q ha hb
    | true =>
      simp only [d106059, d106822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d106097 q = 1) (hb : d106823 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106097, d106823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d106097, d106823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d106098 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d106099 q = 1) (hb : d106824 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106099, d106824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106099, d106824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d106100 q = 1) (hb : d106825 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106100, d106825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d106100, d106825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d106101 q = 1) (hb : d106826 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106101, d106826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106101, d106826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d106107 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d106111 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d106113 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d106068 q = 1) (hb : d106831 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106068, d106831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15101 q ha hb
    | true =>
      simp only [d106068, d106831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d106114 q = 1) (hb : d106832 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106114, d106832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d106114, d106832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d106115 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d106116 q = 1) (hb : d106833 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106116, d106833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d106116, d106833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d106117 q = 1) (hb : d106834 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106117, d106834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d106117, d106834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d106118 q = 1) (hb : d106835 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106118, d106835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d106118, d106835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d106119 q = 1) (hb : d106836 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106119, d106836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d106119, d106836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro15205 (p : Pattern) (ha : d106128 p = 1) (hb : d107116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d106113 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d106068 q = 1) (hb : d106831 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106068, d106831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15101 q ha hb
    | true =>
      simp only [d106068, d106831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d106114 q = 1) (hb : d106832 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106114, d106832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d106114, d106832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d106115 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d106116 q = 1) (hb : d106833 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106116, d106833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106116, d106833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d106126 q = 1) (hb : d106834 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106126, d106834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106126, d106834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106127 q = 1) (hb : d106835 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106127, d106835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106127, d106835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d106128 q = 1) (hb : d107116 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106128, d107116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106128, d107116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15206 (p : Pattern) (ha : d106155 p = 1) (hb : d107127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d106148 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d106149 q = 1) (hb : d107122 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d106149, d107122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15124 q ha hb
    | true =>
      simp only [d106149, d107122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d106150 q = 1) (hb : d107123 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106150, d107123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d106150, d107123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d106151 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d106152 q = 1) (hb : d107124 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106152, d107124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106152, d107124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d106153 q = 1) (hb : d107125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106153, d107125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106153, d107125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106154 q = 1) (hb : d107126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106154, d107126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106154, d107126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d106155 q = 1) (hb : d107127 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106155, d107127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106155, d107127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15207 (p : Pattern) (ha : d106161 p = 1) (hb : d107133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d106076 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106120 q = 1) (hb : d106837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d106120, d106837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15203 q ha hb
    | true =>
      simp only [d106120, d106837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15204 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d106122 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d106123 q = 1) (hb : d106838 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106123, d106838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106123, d106838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d106124 q = 1) (hb : d107114 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d106124, d107114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106124, d107114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d106125 q = 1) (hb : d107115 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d106125, d107115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106125, d107115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106129 q = 1) (hb : d107117 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d106129, d107117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d106129, d107117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15205 q ha hb
  have h8 (q : Pattern) (ha : d106130 q = 1) (hb : d107118 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106130, d107118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d106130, d107118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d106131 q = 1) (hb : d107119 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d106131, d107119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d106131, d107119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d106132 q = 1) (hb : d107120 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d106132, d107120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d106132, d107120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d106133 q = 1) (hb : d107121 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d106133, d107121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d106133, d107121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d106156 q = 1) (hb : d107128 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d106156, d107128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d106156, d107128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15206 q ha hb
  have h13 (q : Pattern) (ha : d106157 q = 1) (hb : d107129 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106157, d107129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d106157, d107129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d106158 q = 1) (hb : d107130 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d106158, d107130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d106158, d107130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d106159 q = 1) (hb : d107131 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d106159, d107131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d106159, d107131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d106160 q = 1) (hb : d107132 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d106160, d107132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d106160, d107132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d106161 q = 1) (hb : d107133 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d106161, d107133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d106161, d107133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro15208 (p : Pattern) (ha : d106167 p = 1) (hb : d107139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106162 q = 1) (hb : d107134 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d106162, d107134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106162, d107134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15207 q ha hb
  have h2 (q : Pattern) (ha : d106163 q = 1) (hb : d107135 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d106163, d107135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106163, d107135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d106164 q = 1) (hb : d107136 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d106164, d107136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106164, d107136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d106165 q = 1) (hb : d107137 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d106165, d107137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106165, d107137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d106166 q = 1) (hb : d107138 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d106166, d107138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106166, d107138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d106167 q = 1) (hb : d107139 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d106167, d107139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d106167, d107139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15209 (p : Pattern) (ha : d106173 p = 1) (hb : d107145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d105694 q = 1) (hb : d107026 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d105694, d107026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15178 q hb ha
    | true =>
      simp only [d105694, d107026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15184 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d105811 q = 1) (hb : d107053 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d105811, d107053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d105811, d107053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15190 q ha hb
  have h3 (q : Pattern) (ha : d105812 q = 1) (hb : d107054 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d105812, d107054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105812, d107054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d105929 q = 1) (hb : d107081 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d105929, d107081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d105929, d107081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15196 q ha hb
  have h5 (q : Pattern) (ha : d105930 q = 1) (hb : d107082 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d105930, d107082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d105930, d107082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d105931 q = 1) (hb : d107083 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d105931, d107083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d105931, d107083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106048 q = 1) (hb : d107110 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d106048, d107110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d106048, d107110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15202 q ha hb
  have h8 (q : Pattern) (ha : d106049 q = 1) (hb : d107111 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d106049, d107111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d106049, d107111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d106050 q = 1) (hb : d107112 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d106050, d107112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d106050, d107112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d106051 q = 1) (hb : d107113 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d106051, d107113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d106051, d107113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d106168 q = 1) (hb : d107140 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d106168, d107140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d106168, d107140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15208 q ha hb
  have h12 (q : Pattern) (ha : d106169 q = 1) (hb : d107141 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d106169, d107141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d106169, d107141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d106170 q = 1) (hb : d107142 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d106170, d107142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d106170, d107142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d106171 q = 1) (hb : d107143 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d106171, d107143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d106171, d107143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d106172 q = 1) (hb : d107144 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d106172, d107144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d106172, d107144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d106173 q = 1) (hb : d107145 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d106173, d107145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d106173, d107145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro15210 (p : Pattern) (ha : d106179 p = 1) (hb : d107151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106174 q = 1) (hb : d107146 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d106174, d107146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15209 q ha hb
    | true =>
      simp only [d106174, d107146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106175 q = 1) (hb : d107147 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d106175, d107147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106175, d107147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d106176 q = 1) (hb : d107148 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d106176, d107148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106176, d107148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106177 q = 1) (hb : d107149 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d106177, d107149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106177, d107149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106178 q = 1) (hb : d107150 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d106178, d107150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106178, d107150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106179 q = 1) (hb : d107151 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d106179, d107151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106179, d107151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15211 (p : Pattern) (ha : d106185 p = 1) (hb : d107157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106180 q = 1) (hb : d107152 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d106180, d107152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15210 q ha hb
    | true =>
      simp only [d106180, d107152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106181 q = 1) (hb : d107153 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d106181, d107153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106181, d107153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d106182 q = 1) (hb : d107154 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d106182, d107154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106182, d107154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106183 q = 1) (hb : d107155 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d106183, d107155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106183, d107155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106184 q = 1) (hb : d107156 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d106184, d107156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106184, d107156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106185 q = 1) (hb : d107157 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d106185, d107157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106185, d107157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15212 (p : Pattern) (ha : d106191 p = 1) (hb : d107163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106186 q = 1) (hb : d107158 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d106186, d107158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15211 q ha hb
    | true =>
      simp only [d106186, d107158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106187 q = 1) (hb : d107159 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d106187, d107159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106187, d107159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d106188 q = 1) (hb : d107160 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d106188, d107160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106188, d107160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106189 q = 1) (hb : d107161 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d106189, d107161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106189, d107161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106190 q = 1) (hb : d107162 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d106190, d107162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106190, d107162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106191 q = 1) (hb : d107163 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d106191, d107163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106191, d107163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15213 (p : Pattern) (ha : d106197 p = 1) (hb : d107169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106192 q = 1) (hb : d107164 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d106192, d107164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15212 q ha hb
    | true =>
      simp only [d106192, d107164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106193 q = 1) (hb : d107165 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d106193, d107165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106193, d107165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d106194 q = 1) (hb : d107166 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d106194, d107166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106194, d107166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106195 q = 1) (hb : d107167 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d106195, d107167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106195, d107167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106196 q = 1) (hb : d107168 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d106196, d107168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106196, d107168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106197 q = 1) (hb : d107169 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d106197, d107169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106197, d107169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15214 (p : Pattern) (ha : d106203 p = 1) (hb : d107175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106198 q = 1) (hb : d107170 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d106198, d107170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15213 q ha hb
    | true =>
      simp only [d106198, d107170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106199 q = 1) (hb : d107171 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d106199, d107171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106199, d107171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d106200 q = 1) (hb : d107172 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d106200, d107172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106200, d107172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106201 q = 1) (hb : d107173 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d106201, d107173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106201, d107173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106202 q = 1) (hb : d107174 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d106202, d107174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106202, d107174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106203 q = 1) (hb : d107175 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d106203, d107175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106203, d107175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15215 (p : Pattern) (ha : d106209 p = 1) (hb : d107181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106204 q = 1) (hb : d107176 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d106204, d107176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15214 q ha hb
    | true =>
      simp only [d106204, d107176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106205 q = 1) (hb : d107177 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d106205, d107177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106205, d107177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d106206 q = 1) (hb : d107178 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d106206, d107178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106206, d107178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106207 q = 1) (hb : d107179 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d106207, d107179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106207, d107179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106208 q = 1) (hb : d107180 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d106208, d107180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106208, d107180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106209 q = 1) (hb : d107181 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d106209, d107181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106209, d107181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15216 (p : Pattern) (ha : d106215 p = 1) (hb : d107187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106210 q = 1) (hb : d107182 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d106210, d107182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15215 q ha hb
    | true =>
      simp only [d106210, d107182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d106211 q = 1) (hb : d107183 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d106211, d107183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106211, d107183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d106212 q = 1) (hb : d107184 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d106212, d107184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106212, d107184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d106213 q = 1) (hb : d107185 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d106213, d107185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106213, d107185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d106214 q = 1) (hb : d107186 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d106214, d107186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106214, d107186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d106215 q = 1) (hb : d107187 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d106215, d107187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106215, d107187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro15217 (p : Pattern) (ha : d88199 p = 1) (hb : d107192 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d104620 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d104626 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d104634 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d88195 q = 1) (hb : d107188 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88195, d107188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88195, d107188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d104554 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d88196 q = 1) (hb : d107189 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88196, d107189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88196, d107189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88197 q = 1) (hb : d107190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88197, d107190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88197, d107190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88198 q = 1) (hb : d107191 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88198, d107191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88198, d107191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88199 q = 1) (hb : d107192 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88199, d107192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88199, d107192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro15218 (p : Pattern) (ha : d88206 p = 1) (hb : d107197 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104620 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d104626 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d104634 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d88195 q = 1) (hb : d107188 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88195, d107188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88195, d107188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d104554 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d88196 q = 1) (hb : d107189 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88196, d107189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88196, d107189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88197 q = 1) (hb : d107190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88197, d107190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88197, d107190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88198 q = 1) (hb : d107191 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88198, d107191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88198, d107191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d104652 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d104656 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d104658 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d88154 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d88202 q = 1) (hb : d107193 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88202, d107193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d88202, d107193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d104561 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d88203 q = 1) (hb : d107194 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88203, d107194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88203, d107194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88204 q = 1) (hb : d107195 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88204, d107195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88204, d107195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d88205 q = 1) (hb : d107196 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88205, d107196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88205, d107196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d88206 q = 1) (hb : d107197 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88206, d107197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88206, d107197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro15219 (p : Pattern) (ha : d89102 p = 1) (hb : d107204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d104658 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88202 q = 1) (hb : d107193 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88202, d107193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88202, d107193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d104561 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d88203 q = 1) (hb : d107194 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88203, d107194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88203, d107194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88204 q = 1) (hb : d107202 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88204, d107202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88204, d107202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88205 q = 1) (hb : d107203 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88205, d107203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88205, d107203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d89102 q = 1) (hb : d107204 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89102, d107204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89102, d107204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15220 (p : Pattern) (ha : d89112 p = 1) (hb : d107214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d104687 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88178 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d89108 q = 1) (hb : d107210 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89108, d107210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89108, d107210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d104584 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89109 q = 1) (hb : d107211 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89109, d107211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89109, d107211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89110 q = 1) (hb : d107212 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89110, d107212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89110, d107212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89111 q = 1) (hb : d107213 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89111, d107213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89111, d107213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d89112 q = 1) (hb : d107214 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89112, d107214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89112, d107214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15221 (p : Pattern) (ha : d89118 p = 1) (hb : d107220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104614 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88207 q = 1) (hb : d107198 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88207, d107198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15217 q ha hb
    | true =>
      simp only [d88207, d107198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15218 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d104668 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88208 q = 1) (hb : d107199 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88208, d107199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88208, d107199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89100 q = 1) (hb : d107200 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89100, d107200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89100, d107200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89101 q = 1) (hb : d107201 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89101, d107201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89101, d107201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89103 q = 1) (hb : d107205 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89103, d107205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89103, d107205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15219 q ha hb
  have h8 (q : Pattern) (ha : d89104 q = 1) (hb : d107206 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89104, d107206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d89104, d107206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d89105 q = 1) (hb : d107207 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89105, d107207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d89105, d107207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d89106 q = 1) (hb : d107208 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89106, d107208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d89106, d107208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d89107 q = 1) (hb : d107209 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89107, d107209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89107, d107209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d89113 q = 1) (hb : d107215 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89113, d107215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89113, d107215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15220 q ha hb
  have h13 (q : Pattern) (ha : d89114 q = 1) (hb : d107216 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89114, d107216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d89114, d107216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d89115 q = 1) (hb : d107217 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89115, d107217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d89115, d107217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d89116 q = 1) (hb : d107218 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89116, d107218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d89116, d107218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d89117 q = 1) (hb : d107219 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89117, d107219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89117, d107219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d89118 q = 1) (hb : d107220 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89118, d107220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d89118, d107220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro15222 (p : Pattern) (ha : d89124 p = 1) (hb : d107226 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104599 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d89119 q = 1) (hb : d107221 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89119, d107221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89119, d107221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15221 q ha hb
  have h3 (q : Pattern) (ha : d89120 q = 1) (hb : d107222 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89120, d107222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89120, d107222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89121 q = 1) (hb : d107223 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89121, d107223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89121, d107223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d89122 q = 1) (hb : d107224 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89122, d107224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89122, d107224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89123 q = 1) (hb : d107225 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89123, d107225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89123, d107225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89124 q = 1) (hb : d107226 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d89124, d107226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89124, d107226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro15223 (p : Pattern) (ha : d106284 p = 1) (hb : d107231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d104740 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d104746 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d104754 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d106279 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d106280 q = 1) (hb : d107227 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106280, d107227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106280, d107227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d104764 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d106281 q = 1) (hb : d107228 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106281, d107228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106281, d107228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d106282 q = 1) (hb : d107229 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106282, d107229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106282, d107229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d106283 q = 1) (hb : d107230 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106283, d107230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106283, d107230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d106284 q = 1) (hb : d107231 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106284, d107231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d106284, d107231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro15224 (p : Pattern) (ha : d106293 p = 1) (hb : d107236 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d104746 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d104754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d106279 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d106280 q = 1) (hb : d107227 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106280, d107227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106280, d107227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d104764 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d106281 q = 1) (hb : d107228 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106281, d107228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106281, d107228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106282 q = 1) (hb : d107229 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106282, d107229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106282, d107229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d106283 q = 1) (hb : d107230 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106283, d107230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d106283, d107230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d104773 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d104777 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d104779 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d106288 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d106289 q = 1) (hb : d107232 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106289, d107232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d106289, d107232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d104783 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d106290 q = 1) (hb : d107233 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106290, d107233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d106290, d107233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d106291 q = 1) (hb : d107234 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106291, d107234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d106291, d107234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d106292 q = 1) (hb : d107235 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106292, d107235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d106292, d107235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d106293 q = 1) (hb : d107236 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106293, d107236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d106293, d107236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro15225 (p : Pattern) (ha : d107003 p = 1) (hb : d107243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d104779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d106288 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d106289 q = 1) (hb : d107232 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106289, d107232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106289, d107232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d104783 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d106290 q = 1) (hb : d107233 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106290, d107233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106290, d107233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d106291 q = 1) (hb : d107241 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106291, d107241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d106291, d107241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106292 q = 1) (hb : d107242 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106292, d107242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d106292, d107242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107003 q = 1) (hb : d107243 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107003, d107243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107003, d107243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15226 (p : Pattern) (ha : d107013 p = 1) (hb : d107253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d104813 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d106369 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107009 q = 1) (hb : d107249 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107009, d107249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107009, d107249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d104824 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107010 q = 1) (hb : d107250 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107010, d107250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107010, d107250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107011 q = 1) (hb : d107251 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107011, d107251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107011, d107251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107012 q = 1) (hb : d107252 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107012, d107252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107012, d107252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107013 q = 1) (hb : d107253 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107013, d107253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107013, d107253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15227 (p : Pattern) (ha : d107019 p = 1) (hb : d107259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106294 q = 1) (hb : d107237 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d106294, d107237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15223 q ha hb
    | true =>
      simp only [d106294, d107237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15224 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d104790 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d106295 q = 1) (hb : d107238 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106295, d107238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106295, d107238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107001 q = 1) (hb : d107239 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107001, d107239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107001, d107239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107002 q = 1) (hb : d107240 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107002, d107240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107002, d107240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107004 q = 1) (hb : d107244 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107004, d107244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107004, d107244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15225 q ha hb
  have h8 (q : Pattern) (ha : d107005 q = 1) (hb : d107245 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107005, d107245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107005, d107245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d107006 q = 1) (hb : d107246 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107006, d107246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107006, d107246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d107007 q = 1) (hb : d107247 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107007, d107247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107007, d107247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d107008 q = 1) (hb : d107248 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107008, d107248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107008, d107248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107014 q = 1) (hb : d107254 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107014, d107254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107014, d107254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15226 q ha hb
  have h13 (q : Pattern) (ha : d107015 q = 1) (hb : d107255 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107015, d107255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107015, d107255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d107016 q = 1) (hb : d107256 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107016, d107256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107016, d107256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d107017 q = 1) (hb : d107257 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107017, d107257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d107017, d107257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d107018 q = 1) (hb : d107258 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107018, d107258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107018, d107258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d107019 q = 1) (hb : d107259 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107019, d107259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107019, d107259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro15228 (p : Pattern) (ha : d107025 p = 1) (hb : d107265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107020 q = 1) (hb : d107260 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107020, d107260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107020, d107260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15227 q ha hb
  have h2 (q : Pattern) (ha : d107021 q = 1) (hb : d107261 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107021, d107261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107021, d107261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107022 q = 1) (hb : d107262 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107022, d107262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107022, d107262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107023 q = 1) (hb : d107263 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107023, d107263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107023, d107263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107024 q = 1) (hb : d107264 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107024, d107264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107024, d107264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107025 q = 1) (hb : d107265 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d107025, d107265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107025, d107265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15229 (p : Pattern) (ha : d106401 p = 1) (hb : d107271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d104872 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d104878 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d104886 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d106396 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d106397 q = 1) (hb : d107267 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106397, d107267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106397, d107267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d104896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d106398 q = 1) (hb : d107268 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106398, d107268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106398, d107268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d106399 q = 1) (hb : d107269 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106399, d107269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106399, d107269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d106400 q = 1) (hb : d107270 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106400, d107270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106400, d107270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d106401 q = 1) (hb : d107271 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106401, d107271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d106401, d107271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro15230 (p : Pattern) (ha : d106410 p = 1) (hb : d107276 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104872 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d104878 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d104886 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d106396 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d106397 q = 1) (hb : d107267 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106397, d107267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106397, d107267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d104896 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d106398 q = 1) (hb : d107268 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106398, d107268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106398, d107268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106399 q = 1) (hb : d107269 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106399, d107269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106399, d107269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d106400 q = 1) (hb : d107270 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106400, d107270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d106400, d107270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d104905 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d104909 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d104911 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d106405 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d106406 q = 1) (hb : d107272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106406, d107272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d106406, d107272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d104915 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d106407 q = 1) (hb : d107273 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106407, d107273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d106407, d107273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d106408 q = 1) (hb : d107274 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106408, d107274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d106408, d107274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d106409 q = 1) (hb : d107275 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106409, d107275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d106409, d107275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d106410 q = 1) (hb : d107276 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106410, d107276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d106410, d107276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro15231 (p : Pattern) (ha : d107029 p = 1) (hb : d107283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d104911 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d106405 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d106406 q = 1) (hb : d107272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106406, d107272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106406, d107272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d104915 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d106407 q = 1) (hb : d107273 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106407, d107273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106407, d107273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d106408 q = 1) (hb : d107281 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106408, d107281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d106408, d107281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106409 q = 1) (hb : d107282 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106409, d107282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d106409, d107282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107029 q = 1) (hb : d107283 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107029, d107283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107029, d107283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15232 (p : Pattern) (ha : d107040 p = 1) (hb : d107293 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d104948 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107035 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107036 q = 1) (hb : d107289 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107036, d107289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107036, d107289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d104959 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107037 q = 1) (hb : d107290 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107037, d107290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107037, d107290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107038 q = 1) (hb : d107291 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107038, d107291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107038, d107291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107039 q = 1) (hb : d107292 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107039, d107292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107039, d107292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107040 q = 1) (hb : d107293 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107040, d107293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107040, d107293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15233 (p : Pattern) (ha : d107046 p = 1) (hb : d107299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104866 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106411 q = 1) (hb : d107277 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d106411, d107277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15229 q ha hb
    | true =>
      simp only [d106411, d107277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15230 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d104922 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d106412 q = 1) (hb : d107278 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106412, d107278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106412, d107278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107027 q = 1) (hb : d107279 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107027, d107279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107027, d107279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107028 q = 1) (hb : d107280 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107028, d107280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107028, d107280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107030 q = 1) (hb : d107284 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107030, d107284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107030, d107284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15231 q ha hb
  have h8 (q : Pattern) (ha : d107031 q = 1) (hb : d107285 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107031, d107285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107031, d107285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d107032 q = 1) (hb : d107286 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107032, d107286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107032, d107286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d107033 q = 1) (hb : d107287 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107033, d107287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107033, d107287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d107034 q = 1) (hb : d107288 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107034, d107288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107034, d107288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107041 q = 1) (hb : d107294 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107041, d107294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107041, d107294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15232 q ha hb
  have h13 (q : Pattern) (ha : d107042 q = 1) (hb : d107295 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107042, d107295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107042, d107295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d107043 q = 1) (hb : d107296 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107043, d107296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107043, d107296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d107044 q = 1) (hb : d107297 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107044, d107297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d107044, d107297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d107045 q = 1) (hb : d107298 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107045, d107298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107045, d107298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d107046 q = 1) (hb : d107299 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107046, d107299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107046, d107299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro15234 (p : Pattern) (ha : d107052 p = 1) (hb : d107305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107047 q = 1) (hb : d107300 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107047, d107300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107047, d107300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15233 q ha hb
  have h2 (q : Pattern) (ha : d107048 q = 1) (hb : d107301 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107048, d107301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107048, d107301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107049 q = 1) (hb : d107302 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107049, d107302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107049, d107302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107050 q = 1) (hb : d107303 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107050, d107303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107050, d107303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107051 q = 1) (hb : d107304 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107051, d107304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107051, d107304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107052 q = 1) (hb : d107305 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d107052, d107305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107052, d107305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15235 (p : Pattern) (ha : d106542 p = 1) (hb : d107312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105008 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105014 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d105022 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d106537 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d106538 q = 1) (hb : d107308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106538, d107308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106538, d107308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d105032 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d106539 q = 1) (hb : d107309 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106539, d107309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106539, d107309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d106540 q = 1) (hb : d107310 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106540, d107310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106540, d107310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d106541 q = 1) (hb : d107311 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106541, d107311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106541, d107311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d106542 q = 1) (hb : d107312 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106542, d107312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d106542, d107312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro15236 (p : Pattern) (ha : d106551 p = 1) (hb : d107317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d105008 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105014 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105022 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d106537 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d106538 q = 1) (hb : d107308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106538, d107308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106538, d107308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d105032 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d106539 q = 1) (hb : d107309 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106539, d107309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106539, d107309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106540 q = 1) (hb : d107310 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106540, d107310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106540, d107310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d106541 q = 1) (hb : d107311 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106541, d107311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d106541, d107311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d105041 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d105045 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d105047 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d106546 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d106547 q = 1) (hb : d107313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106547, d107313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d106547, d107313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d105051 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d106548 q = 1) (hb : d107314 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106548, d107314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d106548, d107314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d106549 q = 1) (hb : d107315 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106549, d107315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d106549, d107315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d106550 q = 1) (hb : d107316 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106550, d107316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d106550, d107316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d106551 q = 1) (hb : d107317 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106551, d107317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d106551, d107317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro15237 (p : Pattern) (ha : d107057 p = 1) (hb : d107324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105047 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d106546 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d106547 q = 1) (hb : d107313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106547, d107313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106547, d107313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d105051 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d106548 q = 1) (hb : d107314 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106548, d107314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106548, d107314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d106549 q = 1) (hb : d107322 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106549, d107322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d106549, d107322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106550 q = 1) (hb : d107323 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106550, d107323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d106550, d107323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107057 q = 1) (hb : d107324 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107057, d107324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107057, d107324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15238 (p : Pattern) (ha : d107068 p = 1) (hb : d107334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105084 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107063 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107064 q = 1) (hb : d107330 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107064, d107330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107064, d107330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d105095 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107065 q = 1) (hb : d107331 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107065, d107331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107065, d107331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107066 q = 1) (hb : d107332 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107066, d107332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107066, d107332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107067 q = 1) (hb : d107333 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107067, d107333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107067, d107333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107068 q = 1) (hb : d107334 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107068, d107334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107068, d107334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15239 (p : Pattern) (ha : d107074 p = 1) (hb : d107340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d105002 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106552 q = 1) (hb : d107318 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d106552, d107318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15235 q ha hb
    | true =>
      simp only [d106552, d107318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15236 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105058 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d106553 q = 1) (hb : d107319 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106553, d107319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106553, d107319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107055 q = 1) (hb : d107320 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107055, d107320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107055, d107320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107056 q = 1) (hb : d107321 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107056, d107321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107056, d107321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107058 q = 1) (hb : d107325 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107058, d107325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107058, d107325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15237 q ha hb
  have h8 (q : Pattern) (ha : d107059 q = 1) (hb : d107326 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107059, d107326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107059, d107326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d107060 q = 1) (hb : d107327 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107060, d107327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107060, d107327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d107061 q = 1) (hb : d107328 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107061, d107328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107061, d107328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d107062 q = 1) (hb : d107329 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107062, d107329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107062, d107329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107069 q = 1) (hb : d107335 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107069, d107335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107069, d107335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15238 q ha hb
  have h13 (q : Pattern) (ha : d107070 q = 1) (hb : d107336 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107070, d107336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107070, d107336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d107071 q = 1) (hb : d107337 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107071, d107337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107071, d107337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d107072 q = 1) (hb : d107338 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107072, d107338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d107072, d107338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d107073 q = 1) (hb : d107339 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107073, d107339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107073, d107339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d107074 q = 1) (hb : d107340 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107074, d107340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107074, d107340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro15240 (p : Pattern) (ha : d107080 p = 1) (hb : d107346 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107075 q = 1) (hb : d107341 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107075, d107341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107075, d107341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15239 q ha hb
  have h2 (q : Pattern) (ha : d107076 q = 1) (hb : d107342 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107076, d107342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107076, d107342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107077 q = 1) (hb : d107343 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107077, d107343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107077, d107343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107078 q = 1) (hb : d107344 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107078, d107344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107078, d107344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107079 q = 1) (hb : d107345 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107079, d107345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107079, d107345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107080 q = 1) (hb : d107346 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d107080, d107346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107080, d107346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15241 (p : Pattern) (ha : d106684 p = 1) (hb : d107354 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105145 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105151 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d105159 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d106679 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d106680 q = 1) (hb : d107350 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106680, d107350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106680, d107350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d105169 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d106681 q = 1) (hb : d107351 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106681, d107351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106681, d107351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d106682 q = 1) (hb : d107352 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106682, d107352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106682, d107352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d106683 q = 1) (hb : d107353 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106683, d107353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106683, d107353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d106684 q = 1) (hb : d107354 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106684, d107354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d106684, d107354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro15242 (p : Pattern) (ha : d106693 p = 1) (hb : d107359 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d105145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105151 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105159 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d106679 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d106680 q = 1) (hb : d107350 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106680, d107350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106680, d107350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d105169 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d106681 q = 1) (hb : d107351 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106681, d107351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106681, d107351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106682 q = 1) (hb : d107352 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106682, d107352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106682, d107352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d106683 q = 1) (hb : d107353 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106683, d107353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d106683, d107353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d105178 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d105182 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d105184 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d106688 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d106689 q = 1) (hb : d107355 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106689, d107355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d106689, d107355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d105188 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d106690 q = 1) (hb : d107356 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106690, d107356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d106690, d107356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d106691 q = 1) (hb : d107357 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106691, d107357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d106691, d107357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d106692 q = 1) (hb : d107358 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106692, d107358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d106692, d107358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d106693 q = 1) (hb : d107359 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106693, d107359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d106693, d107359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro15243 (p : Pattern) (ha : d107086 p = 1) (hb : d107366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105184 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d106688 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d106689 q = 1) (hb : d107355 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106689, d107355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106689, d107355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d105188 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d106690 q = 1) (hb : d107356 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106690, d107356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106690, d107356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d106691 q = 1) (hb : d107364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106691, d107364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d106691, d107364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106692 q = 1) (hb : d107365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106692, d107365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d106692, d107365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107086 q = 1) (hb : d107366 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107086, d107366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107086, d107366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15244 (p : Pattern) (ha : d107097 p = 1) (hb : d107376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105221 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107092 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107093 q = 1) (hb : d107372 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107093, d107372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107093, d107372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d105232 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107094 q = 1) (hb : d107373 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107094, d107373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107094, d107373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107095 q = 1) (hb : d107374 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107095, d107374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107095, d107374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107096 q = 1) (hb : d107375 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107096, d107375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107096, d107375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107097 q = 1) (hb : d107376 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107097, d107376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107097, d107376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15245 (p : Pattern) (ha : d107103 p = 1) (hb : d107382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d105139 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d106694 q = 1) (hb : d107360 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d106694, d107360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15241 q ha hb
    | true =>
      simp only [d106694, d107360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15242 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105195 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d106695 q = 1) (hb : d107361 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106695, d107361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106695, d107361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107084 q = 1) (hb : d107362 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107084, d107362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107084, d107362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107085 q = 1) (hb : d107363 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107085, d107363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107085, d107363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107087 q = 1) (hb : d107367 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107087, d107367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107087, d107367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15243 q ha hb
  have h8 (q : Pattern) (ha : d107088 q = 1) (hb : d107368 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107088, d107368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107088, d107368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d107089 q = 1) (hb : d107369 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107089, d107369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107089, d107369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d107090 q = 1) (hb : d107370 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107090, d107370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107090, d107370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d107091 q = 1) (hb : d107371 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107091, d107371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107091, d107371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107098 q = 1) (hb : d107377 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107098, d107377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107098, d107377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15244 q ha hb
  have h13 (q : Pattern) (ha : d107099 q = 1) (hb : d107378 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107099, d107378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107099, d107378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d107100 q = 1) (hb : d107379 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107100, d107379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107100, d107379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d107101 q = 1) (hb : d107380 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107101, d107380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d107101, d107380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d107102 q = 1) (hb : d107381 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107102, d107381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107102, d107381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d107103 q = 1) (hb : d107382 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107103, d107382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107103, d107382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro15246 (p : Pattern) (ha : d107109 p = 1) (hb : d107388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107104 q = 1) (hb : d107383 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107104, d107383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107104, d107383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15245 q ha hb
  have h2 (q : Pattern) (ha : d107105 q = 1) (hb : d107384 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107105, d107384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107105, d107384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107106 q = 1) (hb : d107385 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107106, d107385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107106, d107385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107107 q = 1) (hb : d107386 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107107, d107386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107107, d107386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107108 q = 1) (hb : d107387 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107108, d107387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107108, d107387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107109 q = 1) (hb : d107388 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d107109, d107388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107109, d107388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15247 (p : Pattern) (ha : d106827 p = 1) (hb : d107397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105283 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105289 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d105297 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d106822 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d106823 q = 1) (hb : d107393 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106823, d107393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106823, d107393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d105307 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d106824 q = 1) (hb : d107394 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106824, d107394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d106824, d107394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d106825 q = 1) (hb : d107395 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106825, d107395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106825, d107395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d106826 q = 1) (hb : d107396 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106826, d107396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106826, d107396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d106827 q = 1) (hb : d107397 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106827, d107397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d106827, d107397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro15248 (p : Pattern) (ha : d106836 p = 1) (hb : d107402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d105283 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105289 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d105297 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d106822 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d106823 q = 1) (hb : d107393 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106823, d107393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106823, d107393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d105307 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d106824 q = 1) (hb : d107394 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106824, d107394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d106824, d107394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106825 q = 1) (hb : d107395 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106825, d107395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106825, d107395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d106826 q = 1) (hb : d107396 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106826, d107396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d106826, d107396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d105316 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d105320 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d105322 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d106831 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d106832 q = 1) (hb : d107398 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106832, d107398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d106832, d107398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d105326 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d106833 q = 1) (hb : d107399 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106833, d107399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d106833, d107399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d106834 q = 1) (hb : d107400 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106834, d107400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d106834, d107400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d106835 q = 1) (hb : d107401 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106835, d107401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d106835, d107401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d106836 q = 1) (hb : d107402 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d106836, d107402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d106836, d107402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro15249 (p : Pattern) (ha : d107116 p = 1) (hb : d107409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d105322 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d106831 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d106832 q = 1) (hb : d107398 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d106832, d107398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106832, d107398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d105326 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d106833 q = 1) (hb : d107399 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d106833, d107399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d106833, d107399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d106834 q = 1) (hb : d107407 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d106834, d107407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d106834, d107407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d106835 q = 1) (hb : d107408 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d106835, d107408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d106835, d107408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107116 q = 1) (hb : d107409 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107116, d107409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107116, d107409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
