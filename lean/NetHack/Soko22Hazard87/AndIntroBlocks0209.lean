import NetHack.Soko22Hazard87.AndIntroBlocks0208
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro52250 (p : Pattern) (ha : d150112 p = 1) (hb : d194388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150107 q = 1) (hb : d194383 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150107, d194383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150107, d194383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52249 q ha hb
  have h2 (q : Pattern) (ha : d150108 q = 1) (hb : d194384 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150108, d194384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150108, d194384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150109 q = 1) (hb : d194385 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150109, d194385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150109, d194385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150110 q = 1) (hb : d194386 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150110, d194386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150110, d194386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150111 q = 1) (hb : d194387 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150111, d194387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150111, d194387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150112 q = 1) (hb : d194388 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150112, d194388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150112, d194388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52251 (p : Pattern) (ha : d21450 p = 1) (hb : d150118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21471 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21480 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21510 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21445 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21446 q = 1) (hb : d150114 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d150114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21446, d150114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21556 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21447 q = 1) (hb : d150115 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d150115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21447, d150115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21448 q = 1) (hb : d150116 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d150116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21448, d150116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21449 q = 1) (hb : d150117 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d150117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21449, d150117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21450 q = 1) (hb : d150118 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21450, d150118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21450, d150118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52252 (p : Pattern) (ha : d21460 p = 1) (hb : d150123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21480 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21510 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21445 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d21446 q = 1) (hb : d150114 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d150114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21446, d150114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21556 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d21447 q = 1) (hb : d150115 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d150115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21447, d150115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21448 q = 1) (hb : d150116 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d150116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21448, d150116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21449 q = 1) (hb : d150117 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d150117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21449, d150117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d21566 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21571 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d21573 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d21455 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21456 q = 1) (hb : d150119 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21456, d150119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21456, d150119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21580 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d21457 q = 1) (hb : d150120 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21457, d150120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21457, d150120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21458 q = 1) (hb : d150121 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21458, d150121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21458, d150121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21459 q = 1) (hb : d150122 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21459, d150122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21459, d150122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d21460 q = 1) (hb : d150123 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21460, d150123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21460, d150123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro52253 (p : Pattern) (ha : d150130 p = 1) (hb : d194392 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21573 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21455 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d21456 q = 1) (hb : d150119 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21456, d150119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21456, d150119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21580 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21457 q = 1) (hb : d150120 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21457, d150120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21457, d150120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21458 q = 1) (hb : d150128 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21458, d150128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21458, d150128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21459 q = 1) (hb : d150129 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21459, d150129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21459, d150129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150130 q = 1) (hb : d194392 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150130, d194392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150130, d194392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro52254 (p : Pattern) (ha : d150140 p = 1) (hb : d194403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21662 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d194398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150136 q = 1) (hb : d194399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150136, d194399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150136, d194399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21706 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150137 q = 1) (hb : d194400 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150137, d194400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150137, d194400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150138 q = 1) (hb : d194401 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150138, d194401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150138, d194401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150139 q = 1) (hb : d194402 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150139, d194402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150139, d194402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150140 q = 1) (hb : d194403 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150140, d194403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150140, d194403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52255 (p : Pattern) (ha : d150146 p = 1) (hb : d194409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21463 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21461 q = 1) (hb : d150124 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21461, d150124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52251 q ha hb
    | true =>
      simp only [d21461, d150124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52252 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21598 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d21462 q = 1) (hb : d150125 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21462, d150125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21462, d150125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150126 q = 1) (hb : d194390 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150126, d194390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150126, d194390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150127 q = 1) (hb : d194391 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150127, d194391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150127, d194391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150131 q = 1) (hb : d194393 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150131, d194393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150131, d194393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52253 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d21607 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150132 q = 1) (hb : d194394 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150132, d194394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150132, d194394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150133 q = 1) (hb : d194395 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150133, d194395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150133, d194395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150134 q = 1) (hb : d194396 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150134, d194396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150134, d194396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150135 q = 1) (hb : d194397 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150135, d194397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150135, d194397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150141 q = 1) (hb : d194404 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150141, d194404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150141, d194404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52254 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21722 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150142 q = 1) (hb : d194405 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150142, d194405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150142, d194405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150143 q = 1) (hb : d194406 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150143, d194406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150143, d194406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150144 q = 1) (hb : d194407 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150144, d194407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150144, d194407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150145 q = 1) (hb : d194408 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150145, d194408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150145, d194408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150146 q = 1) (hb : d194409 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150146, d194409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150146, d194409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro52256 (p : Pattern) (ha : d150152 p = 1) (hb : d194415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150147 q = 1) (hb : d194410 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150147, d194410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150147, d194410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52255 q ha hb
  have h2 (q : Pattern) (ha : d150148 q = 1) (hb : d194411 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150148, d194411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150148, d194411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150149 q = 1) (hb : d194412 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150149, d194412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150149, d194412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150150 q = 1) (hb : d194413 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150150, d194413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150150, d194413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150151 q = 1) (hb : d194414 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150151, d194414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150151, d194414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150152 q = 1) (hb : d194415 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150152, d194415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150152, d194415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52257 (p : Pattern) (ha : d21803 p = 1) (hb : d150159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21824 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21833 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21878 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21798 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21799 q = 1) (hb : d150155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21799, d150155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21799, d150155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21962 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21800 q = 1) (hb : d150156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21800, d150156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21800, d150156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21801 q = 1) (hb : d150157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21801, d150157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21801, d150157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21802 q = 1) (hb : d150158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21802, d150158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21802, d150158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21803 q = 1) (hb : d150159 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21803, d150159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21803, d150159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52258 (p : Pattern) (ha : d21813 p = 1) (hb : d150164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21824 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21833 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21878 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21798 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d21799 q = 1) (hb : d150155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21799, d150155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21799, d150155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21962 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d21800 q = 1) (hb : d150156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21800, d150156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21800, d150156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21801 q = 1) (hb : d150157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21801, d150157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21801, d150157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21802 q = 1) (hb : d150158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21802, d150158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21802, d150158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d21972 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21977 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d21980 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d21808 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21809 q = 1) (hb : d150160 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21809, d150160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21809, d150160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21987 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d21810 q = 1) (hb : d150161 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21810, d150161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21810, d150161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21811 q = 1) (hb : d150162 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21811, d150162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21811, d150162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21812 q = 1) (hb : d150163 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21812, d150163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21812, d150163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d21813 q = 1) (hb : d150164 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21813, d150164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21813, d150164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro52259 (p : Pattern) (ha : d150171 p = 1) (hb : d194420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21808 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d21809 q = 1) (hb : d150160 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21809, d150160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21809, d150160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21987 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21810 q = 1) (hb : d150161 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21810, d150161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21810, d150161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21811 q = 1) (hb : d150169 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21811, d150169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21811, d150169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21812 q = 1) (hb : d150170 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21812, d150170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21812, d150170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150171 q = 1) (hb : d194420 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150171, d194420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150171, d194420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro52260 (p : Pattern) (ha : d150181 p = 1) (hb : d194439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22110 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d194434 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150177 q = 1) (hb : d194435 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150177, d194435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150177, d194435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22188 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150178 q = 1) (hb : d194436 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150178, d194436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150178, d194436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150179 q = 1) (hb : d194437 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150179, d194437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150179, d194437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150180 q = 1) (hb : d194438 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150180, d194438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150180, d194438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150181 q = 1) (hb : d194439 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150181, d194439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150181, d194439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52261 (p : Pattern) (ha : d150187 p = 1) (hb : d194445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21816 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21814 q = 1) (hb : d150165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21814, d150165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52257 q ha hb
    | true =>
      simp only [d21814, d150165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52258 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22010 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d21815 q = 1) (hb : d150166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21815, d150166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21815, d150166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150167 q = 1) (hb : d194418 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150167, d194418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150167, d194418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150168 q = 1) (hb : d194419 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150168, d194419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150168, d194419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150172 q = 1) (hb : d194421 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150172, d194421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150172, d194421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52259 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d22019 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150173 q = 1) (hb : d194422 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150173, d194422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150173, d194422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150174 q = 1) (hb : d194423 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150174, d194423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150174, d194423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150175 q = 1) (hb : d194424 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150175, d194424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150175, d194424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150176 q = 1) (hb : d194425 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150176, d194425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150176, d194425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150182 q = 1) (hb : d194440 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150182, d194440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150182, d194440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52260 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22204 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150183 q = 1) (hb : d194441 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150183, d194441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150183, d194441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150184 q = 1) (hb : d194442 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150184, d194442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150184, d194442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150185 q = 1) (hb : d194443 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150185, d194443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150185, d194443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150186 q = 1) (hb : d194444 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150186, d194444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150186, d194444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150187 q = 1) (hb : d194445 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150187, d194445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150187, d194445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro52262 (p : Pattern) (ha : d150193 p = 1) (hb : d194451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150188 q = 1) (hb : d194446 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150188, d194446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150188, d194446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52261 q ha hb
  have h2 (q : Pattern) (ha : d150189 q = 1) (hb : d194447 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150189, d194447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150189, d194447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150190 q = 1) (hb : d194448 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150190, d194448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150190, d194448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150191 q = 1) (hb : d194449 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150191, d194449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150191, d194449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150192 q = 1) (hb : d194450 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150192, d194450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150192, d194450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150193 q = 1) (hb : d194451 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150193, d194451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150193, d194451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52263 (p : Pattern) (ha : d22281 p = 1) (hb : d150201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22302 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d22351 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22276 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22277 q = 1) (hb : d150197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22277, d150197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22277, d150197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d22435 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d22278 q = 1) (hb : d150198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22278, d150198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22278, d150198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22279 q = 1) (hb : d150199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22279, d150199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22279, d150199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22280 q = 1) (hb : d150200 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22280, d150200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22280, d150200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22281 q = 1) (hb : d150201 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22281, d150201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22281, d150201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52264 (p : Pattern) (ha : d22291 p = 1) (hb : d150206 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22302 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22311 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d22276 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d22277 q = 1) (hb : d150197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22277, d150197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22277, d150197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22435 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22278 q = 1) (hb : d150198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22278, d150198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22278, d150198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22279 q = 1) (hb : d150199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22279, d150199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22279, d150199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22280 q = 1) (hb : d150200 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22280, d150200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22280, d150200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d22445 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22450 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d22453 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d22286 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22287 q = 1) (hb : d150202 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22287, d150202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22287, d150202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22460 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d22288 q = 1) (hb : d150203 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22288, d150203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22288, d150203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22289 q = 1) (hb : d150204 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22289, d150204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22289, d150204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22290 q = 1) (hb : d150205 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22290, d150205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22290, d150205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d22291 q = 1) (hb : d150206 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22291, d150206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22291, d150206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro52265 (p : Pattern) (ha : d150213 p = 1) (hb : d194457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22453 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22286 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d22287 q = 1) (hb : d150202 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22287, d150202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22287, d150202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22460 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22288 q = 1) (hb : d150203 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22288, d150203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22288, d150203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22289 q = 1) (hb : d150211 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22289, d150211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22289, d150211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22290 q = 1) (hb : d150212 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22290, d150212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22290, d150212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150213 q = 1) (hb : d194457 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150213, d194457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150213, d194457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro52266 (p : Pattern) (ha : d150223 p = 1) (hb : d194476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22575 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d194471 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150219 q = 1) (hb : d194472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150219, d194472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150219, d194472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22653 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150220 q = 1) (hb : d194473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150220, d194473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150220, d194473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150221 q = 1) (hb : d194474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150221, d194474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150221, d194474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150222 q = 1) (hb : d194475 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150222, d194475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150222, d194475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150223 q = 1) (hb : d194476 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150223, d194476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150223, d194476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52267 (p : Pattern) (ha : d150229 p = 1) (hb : d194482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22292 q = 1) (hb : d150207 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22292, d150207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52263 q ha hb
    | true =>
      simp only [d22292, d150207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52264 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22483 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d22293 q = 1) (hb : d150208 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22293, d150208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22293, d150208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150209 q = 1) (hb : d194455 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150209, d194455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150209, d194455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150210 q = 1) (hb : d194456 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150210, d194456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150210, d194456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150214 q = 1) (hb : d194458 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150214, d194458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150214, d194458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52265 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d22492 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150215 q = 1) (hb : d194459 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150215, d194459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150215, d194459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150216 q = 1) (hb : d194460 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150216, d194460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150216, d194460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150217 q = 1) (hb : d194461 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150217, d194461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150217, d194461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150218 q = 1) (hb : d194462 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150218, d194462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150218, d194462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150224 q = 1) (hb : d194477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150224, d194477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150224, d194477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52266 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22669 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150225 q = 1) (hb : d194478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150225, d194478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150225, d194478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150226 q = 1) (hb : d194479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150226, d194479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150226, d194479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150227 q = 1) (hb : d194480 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150227, d194480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150227, d194480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150228 q = 1) (hb : d194481 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150228, d194481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150228, d194481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150229 q = 1) (hb : d194482 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150229, d194482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150229, d194482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro52268 (p : Pattern) (ha : d150235 p = 1) (hb : d194488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150230 q = 1) (hb : d194483 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150230, d194483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150230, d194483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52267 q ha hb
  have h2 (q : Pattern) (ha : d150231 q = 1) (hb : d194484 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150231, d194484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150231, d194484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150232 q = 1) (hb : d194485 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150232, d194485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150232, d194485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150233 q = 1) (hb : d194486 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150233, d194486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150233, d194486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150234 q = 1) (hb : d194487 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150234, d194487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150234, d194487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150235 q = 1) (hb : d194488 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150235, d194488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150235, d194488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52269 (p : Pattern) (ha : d22736 p = 1) (hb : d150244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22757 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22766 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d22794 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22731 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22732 q = 1) (hb : d150240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22732, d150240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22732, d150240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d22868 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d22733 q = 1) (hb : d150241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22733, d150241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22733, d150241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22734 q = 1) (hb : d150242 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22734, d150242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22734, d150242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22735 q = 1) (hb : d150243 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22735, d150243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22735, d150243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22736 q = 1) (hb : d150244 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22736, d150244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22736, d150244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52270 (p : Pattern) (ha : d22746 p = 1) (hb : d150249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22757 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22794 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d22731 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d22732 q = 1) (hb : d150240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22732, d150240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22732, d150240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22868 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22733 q = 1) (hb : d150241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22733, d150241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22733, d150241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22734 q = 1) (hb : d150242 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22734, d150242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22734, d150242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22735 q = 1) (hb : d150243 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22735, d150243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22735, d150243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d22878 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22883 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d22886 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d22741 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22742 q = 1) (hb : d150245 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22742, d150245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22742, d150245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22893 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d22743 q = 1) (hb : d150246 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22743, d150246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22743, d150246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22744 q = 1) (hb : d150247 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22744, d150247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22744, d150247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22745 q = 1) (hb : d150248 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22745, d150248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22745, d150248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d22746 q = 1) (hb : d150249 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22746, d150249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22746, d150249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro52271 (p : Pattern) (ha : d150256 p = 1) (hb : d194495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22886 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22741 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d22742 q = 1) (hb : d150245 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22742, d150245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22742, d150245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22893 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22743 q = 1) (hb : d150246 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22743, d150246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22743, d150246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22744 q = 1) (hb : d150254 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22744, d150254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22744, d150254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22745 q = 1) (hb : d150255 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22745, d150255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22745, d150255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150256 q = 1) (hb : d194495 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150256, d194495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150256, d194495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro52272 (p : Pattern) (ha : d150266 p = 1) (hb : d194514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d194509 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150262 q = 1) (hb : d194510 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150262, d194510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150262, d194510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23059 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150263 q = 1) (hb : d194511 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150263, d194511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150263, d194511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150264 q = 1) (hb : d194512 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150264, d194512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150264, d194512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150265 q = 1) (hb : d194513 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150265, d194513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150265, d194513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150266 q = 1) (hb : d194514 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150266, d194514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150266, d194514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52273 (p : Pattern) (ha : d150272 p = 1) (hb : d194520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22747 q = 1) (hb : d150250 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22747, d150250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52269 q ha hb
    | true =>
      simp only [d22747, d150250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52270 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22916 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d22748 q = 1) (hb : d150251 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22748, d150251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22748, d150251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150252 q = 1) (hb : d194493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150252, d194493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150252, d194493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150253 q = 1) (hb : d194494 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150253, d194494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150253, d194494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150257 q = 1) (hb : d194496 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150257, d194496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150257, d194496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52271 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d22925 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150258 q = 1) (hb : d194497 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150258, d194497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150258, d194497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150259 q = 1) (hb : d194498 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150259, d194498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150259, d194498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150260 q = 1) (hb : d194499 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150260, d194499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150260, d194499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150261 q = 1) (hb : d194500 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150261, d194500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150261, d194500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150267 q = 1) (hb : d194515 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150267, d194515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150267, d194515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52272 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23075 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150268 q = 1) (hb : d194516 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150268, d194516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150268, d194516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150269 q = 1) (hb : d194517 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150269, d194517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150269, d194517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150270 q = 1) (hb : d194518 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150270, d194518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150270, d194518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150271 q = 1) (hb : d194519 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150271, d194519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150271, d194519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150272 q = 1) (hb : d194520 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150272, d194520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150272, d194520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro52274 (p : Pattern) (ha : d150278 p = 1) (hb : d194526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150273 q = 1) (hb : d194521 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150273, d194521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150273, d194521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52273 q ha hb
  have h2 (q : Pattern) (ha : d150274 q = 1) (hb : d194522 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150274, d194522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150274, d194522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150275 q = 1) (hb : d194523 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150275, d194523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150275, d194523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150276 q = 1) (hb : d194524 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150276, d194524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150276, d194524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150277 q = 1) (hb : d194525 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150277, d194525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150277, d194525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150278 q = 1) (hb : d194526 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150278, d194526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150278, d194526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52275 (p : Pattern) (ha : d150284 p = 1) (hb : d194532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d150113 q = 1) (hb : d194389 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150113, d194389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52244 q ha hb
    | true =>
      simp only [d150113, d194389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52250 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d150153 q = 1) (hb : d194416 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150153, d194416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150153, d194416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52256 q ha hb
  have h3 (q : Pattern) (ha : d150154 q = 1) (hb : d194417 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150154, d194417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150154, d194417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150194 q = 1) (hb : d194452 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150194, d194452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150194, d194452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52262 q ha hb
  have h5 (q : Pattern) (ha : d150195 q = 1) (hb : d194453 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150195, d194453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150195, d194453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150196 q = 1) (hb : d194454 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150196, d194454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150196, d194454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150236 q = 1) (hb : d194489 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150236, d194489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150236, d194489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52268 q ha hb
  have h8 (q : Pattern) (ha : d150237 q = 1) (hb : d194490 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150237, d194490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150237, d194490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150238 q = 1) (hb : d194491 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150238, d194491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150238, d194491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150239 q = 1) (hb : d194492 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150239, d194492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150239, d194492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150279 q = 1) (hb : d194527 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150279, d194527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150279, d194527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52274 q ha hb
  have h12 (q : Pattern) (ha : d150280 q = 1) (hb : d194528 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150280, d194528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150280, d194528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150281 q = 1) (hb : d194529 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150281, d194529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150281, d194529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150282 q = 1) (hb : d194530 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150282, d194530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150282, d194530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150283 q = 1) (hb : d194531 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d150283, d194531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150283, d194531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d150284 q = 1) (hb : d194532 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d150284, d194532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150284, d194532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro52276 (p : Pattern) (ha : d150290 p = 1) (hb : d194538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150285 q = 1) (hb : d194533 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d150285, d194533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52275 q ha hb
    | true =>
      simp only [d150285, d194533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150286 q = 1) (hb : d194534 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d150286, d194534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150286, d194534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150287 q = 1) (hb : d194535 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d150287, d194535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150287, d194535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150288 q = 1) (hb : d194536 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d150288, d194536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150288, d194536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150289 q = 1) (hb : d194537 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d150289, d194537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150289, d194537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150290 q = 1) (hb : d194538 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d150290, d194538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150290, d194538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52277 (p : Pattern) (ha : d150296 p = 1) (hb : d194544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150291 q = 1) (hb : d194539 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d150291, d194539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52276 q ha hb
    | true =>
      simp only [d150291, d194539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150292 q = 1) (hb : d194540 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d150292, d194540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150292, d194540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150293 q = 1) (hb : d194541 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d150293, d194541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150293, d194541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150294 q = 1) (hb : d194542 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d150294, d194542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150294, d194542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150295 q = 1) (hb : d194543 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d150295, d194543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150295, d194543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150296 q = 1) (hb : d194544 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d150296, d194544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150296, d194544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52278 (p : Pattern) (ha : d150302 p = 1) (hb : d194550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150297 q = 1) (hb : d194545 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d150297, d194545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52277 q ha hb
    | true =>
      simp only [d150297, d194545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150298 q = 1) (hb : d194546 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d150298, d194546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150298, d194546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150299 q = 1) (hb : d194547 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d150299, d194547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150299, d194547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150300 q = 1) (hb : d194548 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d150300, d194548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150300, d194548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150301 q = 1) (hb : d194549 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d150301, d194549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150301, d194549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150302 q = 1) (hb : d194550 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d150302, d194550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150302, d194550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52279 (p : Pattern) (ha : d150308 p = 1) (hb : d194556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150303 q = 1) (hb : d194551 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d150303, d194551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52278 q ha hb
    | true =>
      simp only [d150303, d194551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150304 q = 1) (hb : d194552 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d150304, d194552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150304, d194552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150305 q = 1) (hb : d194553 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d150305, d194553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150305, d194553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150306 q = 1) (hb : d194554 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d150306, d194554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150306, d194554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150307 q = 1) (hb : d194555 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d150307, d194555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150307, d194555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150308 q = 1) (hb : d194556 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d150308, d194556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150308, d194556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52280 (p : Pattern) (ha : d150314 p = 1) (hb : d194562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150309 q = 1) (hb : d194557 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d150309, d194557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52279 q ha hb
    | true =>
      simp only [d150309, d194557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150310 q = 1) (hb : d194558 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d150310, d194558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150310, d194558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150311 q = 1) (hb : d194559 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d150311, d194559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150311, d194559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150312 q = 1) (hb : d194560 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d150312, d194560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150312, d194560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150313 q = 1) (hb : d194561 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d150313, d194561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150313, d194561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150314 q = 1) (hb : d194562 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d150314, d194562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150314, d194562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52281 (p : Pattern) (ha : d150320 p = 1) (hb : d194568 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150315 q = 1) (hb : d194563 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d150315, d194563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52280 q ha hb
    | true =>
      simp only [d150315, d194563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150316 q = 1) (hb : d194564 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d150316, d194564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150316, d194564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150317 q = 1) (hb : d194565 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d150317, d194565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150317, d194565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150318 q = 1) (hb : d194566 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d150318, d194566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150318, d194566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150319 q = 1) (hb : d194567 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d150319, d194567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150319, d194567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150320 q = 1) (hb : d194568 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d150320, d194568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150320, d194568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52282 (p : Pattern) (ha : d150326 p = 1) (hb : d194574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150321 q = 1) (hb : d194569 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d150321, d194569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52281 q ha hb
    | true =>
      simp only [d150321, d194569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150322 q = 1) (hb : d194570 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d150322, d194570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150322, d194570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150323 q = 1) (hb : d194571 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d150323, d194571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150323, d194571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150324 q = 1) (hb : d194572 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d150324, d194572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150324, d194572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150325 q = 1) (hb : d194573 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d150325, d194573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150325, d194573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150326 q = 1) (hb : d194574 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d150326, d194574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150326, d194574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52283 (p : Pattern) (ha : d144 p = 1) (hb : d162092 p = 1) : d4818 p = 1 := by
  have h0 (q : Pattern) (ha : d143 q = 1) (hb : d162091 q = 1) : d143 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144 q = 1) (hb : d162092 q = 1) : d4818 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, d162092, d4818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d144, d162092, d4818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52284 (p : Pattern) (ha : d150 p = 1) (hb : d162092 p = 1) : d12227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d162092 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d162092 q = 1) : d4819 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52283 q ha hb
    | true =>
      simp only [d145, d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d162092 q = 1) : d4820 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d162092 q = 1) : d4821 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d162092 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148 q = 1) (hb : d162092 q = 1) : d12225 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d12225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148, d12225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d162092 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d149 q = 1) (hb : d162092 q = 1) : d12226 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d12226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d149, d12226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150 q = 1) (hb : d162092 q = 1) : d12227 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, d12227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150, d12227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro52285 (p : Pattern) (ha : d203 p = 1) (hb : d162092 p = 1) : d12240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d162092 q = 1) : d12228 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d12228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52284 q ha hb
    | true =>
      simp only [d151, d12228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d162092 q = 1) : d12229 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d12229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d12229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d162092 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d162092 q = 1) : d12230 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d12230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d12230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d162092 q = 1) : d12231 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d12231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d12231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d162092 q = 1) : d12232 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d12232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d12232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d203 q = 1) (hb : d162092 q = 1) : d12240 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, d12240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d203, d12240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro52286 (p : Pattern) (ha : d4349 p = 1) (hb : d162092 p = 1) : d115254 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d162092 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d162092 q = 1) : d12241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d12241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52285 q ha hb
    | true =>
      simp only [d204, d12241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4340 q = 1) (hb : d162092 q = 1) : d115243 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d115243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4340, d115243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d162092 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4341 q = 1) (hb : d162092 q = 1) : d115244 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d115244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4341, d115244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4342 q = 1) (hb : d162092 q = 1) : d115252 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d115252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d115252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4343 q = 1) (hb : d162092 q = 1) : d115253 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d115253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d115253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4349 q = 1) (hb : d162092 q = 1) : d115254 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d115254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d115254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52287 (p : Pattern) (ha : d231 p = 1) (hb : d162092 p = 1) : d6078 p = 1 := by
  have h0 (q : Pattern) (ha : d230 q = 1) (hb : d162091 q = 1) : d230 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d231 q = 1) (hb : d162092 q = 1) : d6078 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d162092, d6078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231, d162092, d6078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52288 (p : Pattern) (ha : d237 p = 1) (hb : d162092 p = 1) : d12261 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d162092 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d162092 q = 1) : d6079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52287 q ha hb
    | true =>
      simp only [d232, d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d162092 q = 1) : d6080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d162092 q = 1) : d6081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d162092 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d235 q = 1) (hb : d162092 q = 1) : d12259 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d12259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235, d12259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d162092 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d236 q = 1) (hb : d162092 q = 1) : d12260 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d12260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236, d12260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237 q = 1) (hb : d162092 q = 1) : d12261 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d12261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237, d12261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro52289 (p : Pattern) (ha : d243 p = 1) (hb : d162092 p = 1) : d12267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d162092 q = 1) : d12262 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d12262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52288 q ha hb
    | true =>
      simp only [d238, d12262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d162092 q = 1) : d12263 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d12263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d12263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d162092 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d240 q = 1) (hb : d162092 q = 1) : d12264 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, d12264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d240, d12264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241 q = 1) (hb : d162092 q = 1) : d12265 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, d12265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d241, d12265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d242 q = 1) (hb : d162092 q = 1) : d12266 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, d12266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242, d12266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d243 q = 1) (hb : d162092 q = 1) : d12267 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, d12267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243, d12267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro52290 (p : Pattern) (ha : d4359 p = 1) (hb : d162092 p = 1) : d115264 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d162092 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d162092 q = 1) : d12268 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d12268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52289 q ha hb
    | true =>
      simp only [d244, d12268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4355 q = 1) (hb : d162092 q = 1) : d115260 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d115260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4355, d115260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d162092 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d162092 q = 1) : d115261 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d115261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4356, d115261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d162092 q = 1) : d115262 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d115262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d115262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d162092 q = 1) : d115263 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d115263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d115263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d162092 q = 1) : d115264 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d115264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d115264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52291 (p : Pattern) (ha : d156 p = 1) (hb : d162092 p = 1) : d12233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d162092 q = 1) : d12228 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d12228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52284 q ha hb
    | true =>
      simp only [d151, d12228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d162092 q = 1) : d12229 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d12229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d12229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d162092 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d162092 q = 1) : d12230 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d12230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d12230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d162092 q = 1) : d12231 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d12231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d12231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d162092 q = 1) : d12232 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d12232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d12232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d156 q = 1) (hb : d162092 q = 1) : d12233 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, d12233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, d12233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro52292 (p : Pattern) (ha : d51643 p = 1) (hb : d162092 p = 1) : d115242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d162092 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d162092 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d162092 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157 q = 1) (hb : d162092 q = 1) : d12234 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d12234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52291 q ha hb
    | true =>
      simp only [d157, d12234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d162092 q = 1) : d115238 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d115238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4335, d115238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d162092 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d162092 q = 1) : d115239 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d115239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d115239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d162092 q = 1) : d115240 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d115240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51641, d115240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d162092 q = 1) : d115241 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d115241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51642, d115241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51643 q = 1) (hb : d162092 q = 1) : d115242 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d115242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d115242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52293 (p : Pattern) (ha : d51646 p = 1) (hb : d162092 p = 1) : d115247 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d162092 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d162092 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d162092 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d162092 q = 1) : d12234 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d12234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52291 q ha hb
    | true =>
      simp only [d157, d12234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d162092 q = 1) : d115238 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d115238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4335, d115238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d162092 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d162092 q = 1) : d115239 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d115239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d115239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d162092 q = 1) : d115240 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d115240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51641, d115240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d162092 q = 1) : d115241 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d115241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51642, d115241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d162092 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d162092 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d162092 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d204 q = 1) (hb : d162092 q = 1) : d12241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d12241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52285 q ha hb
    | true =>
      simp only [d204, d12241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4340 q = 1) (hb : d162092 q = 1) : d115243 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d115243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4340, d115243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d162092 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d4341 q = 1) (hb : d162092 q = 1) : d115244 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d115244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4341, d115244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51644 q = 1) (hb : d162092 q = 1) : d115245 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d115245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51644, d115245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51645 q = 1) (hb : d162092 q = 1) : d115246 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d115246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51645, d115246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51646 q = 1) (hb : d162092 q = 1) : d115247 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d115247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51646, d115247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro52294 (p : Pattern) (ha : d51652 p = 1) (hb : d162092 p = 1) : d115270 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d162092 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51647 q = 1) (hb : d162092 q = 1) : d115248 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d115248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52292 q ha hb
    | true =>
      simp only [d51647, d115248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52293 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d162092 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51648 q = 1) (hb : d162092 q = 1) : d115249 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d115249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51648, d115249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51649 q = 1) (hb : d162092 q = 1) : d115250 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d115250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51649, d115250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51650 q = 1) (hb : d162092 q = 1) : d115251 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d115251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51650, d115251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4350 q = 1) (hb : d162092 q = 1) : d115255 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d115255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4350, d115255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52286 q ha hb
  have h8 (q : Pattern) (ha : d4351 q = 1) (hb : d162092 q = 1) : d115256 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d115256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4351, d115256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d4352 q = 1) (hb : d162092 q = 1) : d115257 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d115257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4352, d115257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4353 q = 1) (hb : d162092 q = 1) : d115258 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d115258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4353, d115258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d51651 q = 1) (hb : d162092 q = 1) : d115259 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d115259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51651, d115259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4360 q = 1) (hb : d162092 q = 1) : d115265 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d115265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4360, d115265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52290 q ha hb
  have h13 (q : Pattern) (ha : d4361 q = 1) (hb : d162092 q = 1) : d115266 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d115266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4361, d115266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d4362 q = 1) (hb : d162092 q = 1) : d115267 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d115267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4362, d115267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d4363 q = 1) (hb : d162092 q = 1) : d115268 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d115268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4363, d115268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d4364 q = 1) (hb : d162092 q = 1) : d115269 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d115269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4364, d115269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d51652 q = 1) (hb : d162092 q = 1) : d115270 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d115270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51652, d115270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro52295 (p : Pattern) (ha : d284 p = 1) (hb : d162092 p = 1) : d12289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d162092 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d162092 q = 1) : d12234 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d12234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52291 q ha hb
    | true =>
      simp only [d157, d12234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d162092 q = 1) : d12285 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d12285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d12285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d162092 q = 1) : d12286 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d12286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d12286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d162092 q = 1) : d12287 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d12287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d12287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d162092 q = 1) : d12288 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d12288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d12288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284 q = 1) (hb : d162092 q = 1) : d12289 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d12289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d12289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro52296 (p : Pattern) (ha : d291 p = 1) (hb : d162092 p = 1) : d12296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d162092 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d162092 q = 1) : d12234 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d12234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52291 q ha hb
    | true =>
      simp only [d157, d12234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d162092 q = 1) : d12285 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d12285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d12285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d162092 q = 1) : d12286 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d12286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d12286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d162092 q = 1) : d12287 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d12287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d12287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d162092 q = 1) : d12288 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d12288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d12288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d162092 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d204 q = 1) (hb : d162092 q = 1) : d12241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d12241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52285 q ha hb
    | true =>
      simp only [d204, d12241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287 q = 1) (hb : d162092 q = 1) : d12292 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d12292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d12292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288 q = 1) (hb : d162092 q = 1) : d12293 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d12293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288, d12293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d289 q = 1) (hb : d162092 q = 1) : d12294 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d12294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d12294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d290 q = 1) (hb : d162092 q = 1) : d12295 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d12295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d12295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d291 q = 1) (hb : d162092 q = 1) : d12296 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d12296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d291, d12296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro52297 (p : Pattern) (ha : d397 p = 1) (hb : d162092 p = 1) : d12373 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d162092 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d162092 q = 1) : d12234 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d12234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52291 q ha hb
    | true =>
      simp only [d157, d12234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d162092 q = 1) : d12285 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d12285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d12285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d162092 q = 1) : d12286 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d12286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d12286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d162092 q = 1) : d12287 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d12287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d12287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d162092 q = 1) : d12288 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d12288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d12288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d162092 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d397 q = 1) (hb : d162092 q = 1) : d12373 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, d12373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d397, d12373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52298 (p : Pattern) (ha : d296 p = 1) (hb : d162092 p = 1) : d12301 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d162092 q = 1) : d12228 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d12228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52284 q ha hb
    | true =>
      simp only [d151, d12228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d162092 q = 1) : d12229 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d12229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d12229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d162092 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d162092 q = 1) : d12230 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d12230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d12230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d162092 q = 1) : d12231 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d12231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d12231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d162092 q = 1) : d12300 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d12300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d12300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d296 q = 1) (hb : d162092 q = 1) : d12301 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d296, d12301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d296, d12301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro52299 (p : Pattern) (ha : d303 p = 1) (hb : d162092 p = 1) : d12308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d162092 q = 1) : d12228 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d12228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52284 q ha hb
    | true =>
      simp only [d151, d12228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d162092 q = 1) : d12229 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d12229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d12229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d162092 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d162092 q = 1) : d12230 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d12230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d12230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d162092 q = 1) : d12306 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d12306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d12306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d162092 q = 1) : d12307 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d12307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d12307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d303 q = 1) (hb : d162092 q = 1) : d12308 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, d12308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, d12308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro52300 (p : Pattern) (ha : d4736 p = 1) (hb : d162092 p = 1) : d12344 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d162092 q = 1) : d12228 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d12228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52284 q ha hb
    | true =>
      simp only [d151, d12228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d162092 q = 1) : d12229 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d12229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d12229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d162092 q = 1) : d12341 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d12341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d12341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d162092 q = 1) : d12342 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d12342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d12342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d162092 q = 1) : d12343 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d12343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d12343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4736 q = 1) (hb : d162092 q = 1) : d12344 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, d12344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, d12344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52301 (p : Pattern) (ha : d15966 p = 1) (hb : d162092 p = 1) : d4913 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d322 q = 1) : d322 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d116750 q = 1) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
    | true =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d140 q = 1) (hb : d116750 q = 1) : d752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d141 q = 1) (hb : d116750 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d141, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142 q = 1) (hb : d116750 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d142, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d323 q = 1) (hb : d162091 q = 1) : d755 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d162091, d755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d323, d162091, d755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d12495 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15966 q = 1) (hb : d162092 q = 1) : d4913 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15966, d162092, d4913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15966, d162092, d4913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro52302 (p : Pattern) (ha : d15972 p = 1) (hb : d162092 p = 1) : d162101 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d162092 q = 1) : d162096 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d162096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52301 q ha hb
    | true =>
      simp only [d15967, d162096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52283 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d162092 q = 1) : d162097 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d162097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d162097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d162092 q = 1) : d162098 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d162098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d162098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d162092 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d162092 q = 1) : d4819 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52283 q ha hb
    | true =>
      simp only [d145, d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d162092 q = 1) : d4820 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d162092 q = 1) : d4821 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15970 q = 1) (hb : d162092 q = 1) : d162099 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d162099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d162099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d162092 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d148 q = 1) (hb : d162092 q = 1) : d12225 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d12225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148, d12225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15971 q = 1) (hb : d162092 q = 1) : d162100 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15971, d162100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15971, d162100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15972 q = 1) (hb : d162092 q = 1) : d162101 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15972, d162101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15972, d162101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro52303 (p : Pattern) (ha : d15978 p = 1) (hb : d162092 p = 1) : d162107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d162092 q = 1) : d162102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d162102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52302 q ha hb
    | true =>
      simp only [d15973, d162102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d162092 q = 1) : d162103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d162103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d162103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d162092 q = 1) : d12228 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d12228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52284 q ha hb
    | true =>
      simp only [d151, d12228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d162092 q = 1) : d12229 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d12229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d12229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d162092 q = 1) : d162104 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d162104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d162104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d162092 q = 1) : d162105 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d162105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d162105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d162092 q = 1) : d162106 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d162106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d162106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15978 q = 1) (hb : d162092 q = 1) : d162107 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15978, d162107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15978, d162107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52304 (p : Pattern) (ha : d128195 p = 1) (hb : d162092 p = 1) : d162113 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d162092 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d162092 q = 1) : d12302 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d12302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52298 q ha hb
    | true =>
      simp only [d297, d12302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d162092 q = 1) : d12303 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d12303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d12303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d162092 q = 1) : d12304 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d12304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d12304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d162092 q = 1) : d12305 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d12305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d12305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d162092 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d162092 q = 1) : d12309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d12309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52299 q ha hb
    | true =>
      simp only [d304, d12309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d162092 q = 1) : d12310 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d12310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d12310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d162092 q = 1) : d12311 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d12311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d12311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15979 q = 1) (hb : d162092 q = 1) : d162108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d162108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52303 q ha hb
    | true =>
      simp only [d15979, d162108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52291 q ha hb
  have h11 (q : Pattern) (ha : d128191 q = 1) (hb : d162092 q = 1) : d162109 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d162109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128191, d162109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d162092 q = 1) : d12345 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d12345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52300 q ha hb
    | true =>
      simp only [d4737, d12345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d162092 q = 1) : d12346 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d12346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d12346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d128192 q = 1) (hb : d162092 q = 1) : d162110 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d162110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128192, d162110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128193 q = 1) (hb : d162092 q = 1) : d162111 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d162111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128193, d162111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128194 q = 1) (hb : d162092 q = 1) : d162112 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d162112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128194, d162112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128195 q = 1) (hb : d162092 q = 1) : d162113 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128195, d162113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128195, d162113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro52305 (p : Pattern) (ha : d376 p = 1) (hb : d162092 p = 1) : d12351 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d162092 q = 1) : d12228 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d12228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52284 q ha hb
    | true =>
      simp only [d151, d12228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d162092 q = 1) : d12229 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d12229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d12229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d162092 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d162092 q = 1) : d12230 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d12230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d12230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d162092 q = 1) : d12231 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d12231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d12231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d162092 q = 1) : d12300 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d12300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d12300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d376 q = 1) (hb : d162092 q = 1) : d12351 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376, d12351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d376, d12351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro52306 (p : Pattern) (ha : d381 p = 1) (hb : d162092 p = 1) : d12356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d162092 q = 1) : d12228 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d12228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52284 q ha hb
    | true =>
      simp only [d151, d12228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d162092 q = 1) : d12229 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d12229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d12229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d162092 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d162092 q = 1) : d12230 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d12230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d12230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d162092 q = 1) : d12306 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d12306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d12306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d162092 q = 1) : d12307 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d12307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d12307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d381 q = 1) (hb : d162092 q = 1) : d12356 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d381, d12356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d381, d12356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro52307 (p : Pattern) (ha : d5355 p = 1) (hb : d162092 p = 1) : d12365 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d162092 q = 1) : d12228 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d12228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52284 q ha hb
    | true =>
      simp only [d151, d12228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d162092 q = 1) : d12229 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d12229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d12229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d162092 q = 1) : d12341 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d12341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d12341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d162092 q = 1) : d12342 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d12342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d12342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d162092 q = 1) : d12343 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d12343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d12343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5355 q = 1) (hb : d162092 q = 1) : d12365 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d12365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5355, d12365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52308 (p : Pattern) (ha : d15985 p = 1) (hb : d162092 p = 1) : d162114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d162092 q = 1) : d162102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d162102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52302 q ha hb
    | true =>
      simp only [d15973, d162102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d162092 q = 1) : d162103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d162103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d162103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d162092 q = 1) : d12228 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d12228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52284 q ha hb
    | true =>
      simp only [d151, d12228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d162092 q = 1) : d12229 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d12229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d12229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d162092 q = 1) : d162104 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d162104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d162104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d162092 q = 1) : d162105 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d162105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d162105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d162092 q = 1) : d162106 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d162106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d162106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15985 q = 1) (hb : d162092 q = 1) : d162114 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15985, d162114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15985, d162114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52309 (p : Pattern) (ha : d128200 p = 1) (hb : d162092 p = 1) : d162120 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d162092 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d162092 q = 1) : d12302 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d12302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52298 q ha hb
    | true =>
      simp only [d297, d12302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d162092 q = 1) : d12303 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d12303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d12303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d162092 q = 1) : d12304 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d12304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d12304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d162092 q = 1) : d12305 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d12305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d12305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d162092 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d162092 q = 1) : d12309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d12309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52299 q ha hb
    | true =>
      simp only [d304, d12309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d162092 q = 1) : d12310 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d12310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d12310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d162092 q = 1) : d12311 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d12311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d12311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15979 q = 1) (hb : d162092 q = 1) : d162108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d162108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52303 q ha hb
    | true =>
      simp only [d15979, d162108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52291 q ha hb
  have h11 (q : Pattern) (ha : d128191 q = 1) (hb : d162092 q = 1) : d162109 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d162109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128191, d162109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d162092 q = 1) : d12345 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d12345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52300 q ha hb
    | true =>
      simp only [d4737, d12345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d162092 q = 1) : d12346 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d12346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d12346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d128192 q = 1) (hb : d162092 q = 1) : d162110 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d162110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128192, d162110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128193 q = 1) (hb : d162092 q = 1) : d162111 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d162111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128193, d162111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128194 q = 1) (hb : d162092 q = 1) : d162112 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d162112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128194, d162112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d162092 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d377 q = 1) (hb : d162092 q = 1) : d12352 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d12352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52305 q ha hb
    | true =>
      simp only [d377, d12352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d378 q = 1) (hb : d162092 q = 1) : d12353 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d12353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d378, d12353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d379 q = 1) (hb : d162092 q = 1) : d12354 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d12354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d379, d12354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d380 q = 1) (hb : d162092 q = 1) : d12355 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d12355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d12355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d162092 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d382 q = 1) (hb : d162092 q = 1) : d12357 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d12357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52306 q ha hb
    | true =>
      simp only [d382, d12357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d383 q = 1) (hb : d162092 q = 1) : d12358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d12358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d383, d12358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d384 q = 1) (hb : d162092 q = 1) : d12359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d12359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d384, d12359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d15986 q = 1) (hb : d162092 q = 1) : d162115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d162115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52308 q ha hb
    | true =>
      simp only [d15986, d162115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52285 q ha hb
  have h27 (q : Pattern) (ha : d128196 q = 1) (hb : d162092 q = 1) : d162116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d162116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d128196, d162116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d5356 q = 1) (hb : d162092 q = 1) : d12366 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d12366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52307 q ha hb
    | true =>
      simp only [d5356, d12366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d5357 q = 1) (hb : d162092 q = 1) : d12367 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d12367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d5357, d12367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d128197 q = 1) (hb : d162092 q = 1) : d162117 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d162117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d128197, d162117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d128198 q = 1) (hb : d162092 q = 1) : d162118 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128198, d162118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d128198, d162118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d128199 q = 1) (hb : d162092 q = 1) : d162119 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128199, d162119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128199, d162119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d128200 q = 1) (hb : d162092 q = 1) : d162120 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128200, d162120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128200, d162120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro52310 (p : Pattern) (ha : d128207 p = 1) (hb : d162092 p = 1) : d162127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15986 q = 1) (hb : d162092 q = 1) : d162115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d162115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52308 q ha hb
    | true =>
      simp only [d15986, d162115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52285 q ha hb
  have h2 (q : Pattern) (ha : d128196 q = 1) (hb : d162092 q = 1) : d162116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d162116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128196, d162116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d162092 q = 1) : d12366 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d12366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52307 q ha hb
    | true =>
      simp only [d5356, d12366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5357 q = 1) (hb : d162092 q = 1) : d12367 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d12367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5357, d12367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128197 q = 1) (hb : d162092 q = 1) : d162117 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d162117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128197, d162117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128205 q = 1) (hb : d162092 q = 1) : d162125 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128205, d162125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128205, d162125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128206 q = 1) (hb : d162092 q = 1) : d162126 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128206, d162126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128206, d162126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128207 q = 1) (hb : d162092 q = 1) : d162127 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128207, d162127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128207, d162127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52311 (p : Pattern) (ha : d5377 p = 1) (hb : d162092 p = 1) : d12418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d162092 q = 1) : d12262 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d12262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52288 q ha hb
    | true =>
      simp only [d238, d12262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d162092 q = 1) : d12263 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d12263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d12263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5374 q = 1) (hb : d162092 q = 1) : d12415 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, d12415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, d12415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5375 q = 1) (hb : d162092 q = 1) : d12416 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, d12416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5375, d12416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5376 q = 1) (hb : d162092 q = 1) : d12417 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, d12417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5376, d12417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5377 q = 1) (hb : d162092 q = 1) : d12418 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, d12418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5377, d12418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52312 (p : Pattern) (ha : d16004 p = 1) (hb : d162092 p = 1) : d6210 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d415 q = 1) : d415 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d226 q = 1) (hb : d116750 q = 1) : d971 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d226, d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
  have h3 (q : Pattern) (ha : d139 q = 1) (hb : d116750 q = 1) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
    | true =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d227 q = 1) (hb : d116750 q = 1) : d972 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d227, d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d140 q = 1) (hb : d116750 q = 1) : d752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d228 q = 1) (hb : d116750 q = 1) : d973 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d228, d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d229 q = 1) (hb : d116750 q = 1) : d974 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d229, d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d416 q = 1) (hb : d162091 q = 1) : d975 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d162091, d975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d416, d162091, d975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d12603 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16004 q = 1) (hb : d162092 q = 1) : d6210 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16004, d162092, d6210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16004, d162092, d6210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro52313 (p : Pattern) (ha : d16010 p = 1) (hb : d162092 p = 1) : d162138 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d162092 q = 1) : d162133 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d162133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52312 q ha hb
    | true =>
      simp only [d16005, d162133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52287 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d162092 q = 1) : d162134 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d162134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d162134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d162092 q = 1) : d162135 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d162135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d162135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d162092 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d162092 q = 1) : d6079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52287 q ha hb
    | true =>
      simp only [d232, d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d162092 q = 1) : d6080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d162092 q = 1) : d6081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d162092 q = 1) : d162136 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d162136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d162136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d162092 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d235 q = 1) (hb : d162092 q = 1) : d12259 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d12259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d235, d12259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16009 q = 1) (hb : d162092 q = 1) : d162137 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16009, d162137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16009, d162137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16010 q = 1) (hb : d162092 q = 1) : d162138 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16010, d162138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16010, d162138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro52314 (p : Pattern) (ha : d16016 p = 1) (hb : d162092 p = 1) : d162144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16011 q = 1) (hb : d162092 q = 1) : d162139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16011, d162139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52313 q ha hb
    | true =>
      simp only [d16011, d162139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16012 q = 1) (hb : d162092 q = 1) : d162140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16012, d162140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16012, d162140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238 q = 1) (hb : d162092 q = 1) : d12262 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d12262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52288 q ha hb
    | true =>
      simp only [d238, d12262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239 q = 1) (hb : d162092 q = 1) : d12263 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d12263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d12263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16013 q = 1) (hb : d162092 q = 1) : d162141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16013, d162141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16013, d162141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16014 q = 1) (hb : d162092 q = 1) : d162142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16014, d162142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16014, d162142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16015 q = 1) (hb : d162092 q = 1) : d162143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16015, d162143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16015, d162143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16016 q = 1) (hb : d162092 q = 1) : d162144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16016, d162144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16016, d162144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52315 (p : Pattern) (ha : d128217 p = 1) (hb : d162092 p = 1) : d162150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16017 q = 1) (hb : d162092 q = 1) : d162145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16017, d162145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52314 q ha hb
    | true =>
      simp only [d16017, d162145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52289 q ha hb
  have h2 (q : Pattern) (ha : d128213 q = 1) (hb : d162092 q = 1) : d162146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128213, d162146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128213, d162146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d162092 q = 1) : d12419 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d12419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52311 q ha hb
    | true =>
      simp only [d5378, d12419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d162092 q = 1) : d12420 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d12420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5379, d12420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128214 q = 1) (hb : d162092 q = 1) : d162147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128214, d162147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128214, d162147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128215 q = 1) (hb : d162092 q = 1) : d162148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128215, d162148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128215, d162148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128216 q = 1) (hb : d162092 q = 1) : d162149 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128216, d162149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128216, d162149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128217 q = 1) (hb : d162092 q = 1) : d162150 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128217, d162150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128217, d162150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52316 (p : Pattern) (ha : d128223 p = 1) (hb : d162092 p = 1) : d162156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d162092 q = 1) : d12290 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d12290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d12290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52295 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d162092 q = 1) : d12291 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d12291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d12291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d162092 q = 1) : d12297 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d12297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52295 q ha hb
    | true =>
      simp only [d292, d12297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52296 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d162092 q = 1) : d12298 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d12298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d12298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d162092 q = 1) : d12299 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d12299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d12299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128201 q = 1) (hb : d162092 q = 1) : d162121 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128201, d162121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52304 q ha hb
    | true =>
      simp only [d128201, d162121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52309 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d162092 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d398 q = 1) (hb : d162092 q = 1) : d12374 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d12374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52297 q ha hb
    | true =>
      simp only [d398, d12374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128202 q = 1) (hb : d162092 q = 1) : d162122 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128202, d162122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128202, d162122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128203 q = 1) (hb : d162092 q = 1) : d162123 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128203, d162123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128203, d162123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d128204 q = 1) (hb : d162092 q = 1) : d162124 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128204, d162124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128204, d162124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128208 q = 1) (hb : d162092 q = 1) : d162128 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128208, d162128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128208, d162128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52310 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d162092 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d128209 q = 1) (hb : d162092 q = 1) : d162129 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128209, d162129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128209, d162129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128210 q = 1) (hb : d162092 q = 1) : d162130 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128210, d162130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128210, d162130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128211 q = 1) (hb : d162092 q = 1) : d162131 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128211, d162131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128211, d162131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d128212 q = 1) (hb : d162092 q = 1) : d162132 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128212, d162132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128212, d162132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d128218 q = 1) (hb : d162092 q = 1) : d162151 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128218, d162151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128218, d162151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52315 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d162092 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d128219 q = 1) (hb : d162092 q = 1) : d162152 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128219, d162152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128219, d162152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d128220 q = 1) (hb : d162092 q = 1) : d162153 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128220, d162153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128220, d162153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128221 q = 1) (hb : d162092 q = 1) : d162154 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128221, d162154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128221, d162154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128222 q = 1) (hb : d162092 q = 1) : d162155 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128222, d162155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128222, d162155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d128223 q = 1) (hb : d162092 q = 1) : d162156 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128223, d162156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128223, d162156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro52317 (p : Pattern) (ha : d128229 p = 1) (hb : d162092 p = 1) : d162162 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d162092 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d162092 q = 1) : d115271 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d115271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d115271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52294 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d162092 q = 1) : d115272 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d115272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d115272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d162092 q = 1) : d115273 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d115273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d115273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d162092 q = 1) : d115274 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d115274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d115274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d162092 q = 1) : d115275 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d115275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51657, d115275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128224 q = 1) (hb : d162092 q = 1) : d162157 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128224, d162157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128224, d162157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52316 q ha hb
  have h8 (q : Pattern) (ha : d128225 q = 1) (hb : d162092 q = 1) : d162158 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128225, d162158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128225, d162158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128226 q = 1) (hb : d162092 q = 1) : d162159 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128226, d162159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128226, d162159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128227 q = 1) (hb : d162092 q = 1) : d162160 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128227, d162160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128227, d162160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128228 q = 1) (hb : d162092 q = 1) : d162161 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128228, d162161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128228, d162161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128229 q = 1) (hb : d162092 q = 1) : d162162 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128229, d162162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128229, d162162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro52318 (p : Pattern) (ha : d481 p = 1) (hb : d162092 p = 1) : d12442 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d162092 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d162092 q = 1) : d4819 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52283 q ha hb
    | true =>
      simp only [d145, d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d162092 q = 1) : d4820 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d162092 q = 1) : d4821 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d475 q = 1) (hb : d162092 q = 1) : d4822 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d4822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d475, d4822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d480 q = 1) (hb : d162092 q = 1) : d12441 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d12441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d480, d12441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d481 q = 1) (hb : d162092 q = 1) : d12442 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d12442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d481, d12442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro52319 (p : Pattern) (ha : d491 p = 1) (hb : d162092 p = 1) : d12452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d162092 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52318 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d162092 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d162092 q = 1) : d12449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d162092 q = 1) : d12450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d162092 q = 1) : d12451 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d12451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d12451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d162092 q = 1) : d12452 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d12452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d12452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52320 (p : Pattern) (ha : d501 p = 1) (hb : d162092 p = 1) : d12462 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d162092 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52318 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d162092 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d162092 q = 1) : d12449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d162092 q = 1) : d12450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d162092 q = 1) : d12451 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d12451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d12451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d162092 q = 1) : d12462 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d12462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d12462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52321 (p : Pattern) (ha : d644 p = 1) (hb : d162092 p = 1) : d12580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d162092 q = 1) : d12569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d12569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52319 q ha hb
    | true =>
      simp only [d633, d12569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d162092 q = 1) : d12570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d12570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d12570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d162092 q = 1) : d12571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d12571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, d12571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d162092 q = 1) : d12572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d12572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d12572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d162092 q = 1) : d12573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d12573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d12573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d639 q = 1) (hb : d162092 q = 1) : d12575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d12575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52320 q ha hb
    | true =>
      simp only [d639, d12575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d640 q = 1) (hb : d162092 q = 1) : d12576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d12576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d12576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d641 q = 1) (hb : d162092 q = 1) : d12577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d12577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d641, d12577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d642 q = 1) (hb : d162092 q = 1) : d12578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d12578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d12578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d643 q = 1) (hb : d162092 q = 1) : d12579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d12579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d12579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d644 q = 1) (hb : d162092 q = 1) : d12580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, d12580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d644, d12580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52322 (p : Pattern) (ha : d653 p = 1) (hb : d162092 p = 1) : d12589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d162092 q = 1) : d12575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d12575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52320 q ha hb
    | true =>
      simp only [d639, d12575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d162092 q = 1) : d12576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d12576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d12576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d162092 q = 1) : d12577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d12577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, d12577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d162092 q = 1) : d12578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d12578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d12578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d162092 q = 1) : d12579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d12579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d12579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d162092 q = 1) : d12589 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, d12589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, d12589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52323 (p : Pattern) (ha : d683 p = 1) (hb : d162092 p = 1) : d12622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d162092 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d162092 q = 1) : d6079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52287 q ha hb
    | true =>
      simp only [d232, d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d162092 q = 1) : d6080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d162092 q = 1) : d6081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d673 q = 1) (hb : d162092 q = 1) : d6082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d6082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d673, d6082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d682 q = 1) (hb : d162092 q = 1) : d12621 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d12621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d682, d12621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d683 q = 1) (hb : d162092 q = 1) : d12622 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d12622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d683, d12622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro52324 (p : Pattern) (ha : d730 p = 1) (hb : d162092 p = 1) : d12668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d162092 q = 1) : d12623 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d12623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52323 q ha hb
    | true =>
      simp only [d684, d12623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d162092 q = 1) : d12624 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d12624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d12624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d162092 q = 1) : d12665 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d12665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d12665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d162092 q = 1) : d12666 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d12666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d12666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d162092 q = 1) : d12667 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d12667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d12667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d162092 q = 1) : d12668 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d12668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d12668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52325 (p : Pattern) (ha : d736 p = 1) (hb : d162092 p = 1) : d12674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d162092 q = 1) : d12669 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d12669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52324 q ha hb
    | true =>
      simp only [d731, d12669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d162092 q = 1) : d12670 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d12670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, d12670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d162092 q = 1) : d12671 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d12671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, d12671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d162092 q = 1) : d12672 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, d12672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, d12672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d162092 q = 1) : d12673 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, d12673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, d12673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d162092 q = 1) : d12674 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, d12674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, d12674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52326 (p : Pattern) (ha : d16036 p = 1) (hb : d162092 p = 1) : d162164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d162092 q = 1) : d162096 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d162096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52301 q ha hb
    | true =>
      simp only [d15967, d162096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52283 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d162092 q = 1) : d162097 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d162097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d162097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d162092 q = 1) : d162098 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d162098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d162098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d162092 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d162092 q = 1) : d4819 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52283 q ha hb
    | true =>
      simp only [d145, d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d162092 q = 1) : d4820 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d162092 q = 1) : d4821 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15970 q = 1) (hb : d162092 q = 1) : d162099 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d162099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d162099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d475 q = 1) (hb : d162092 q = 1) : d4822 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d4822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d475, d4822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16035 q = 1) (hb : d162092 q = 1) : d162163 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16035, d162163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16035, d162163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16036 q = 1) (hb : d162092 q = 1) : d162164 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16036, d162164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16036, d162164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro52327 (p : Pattern) (ha : d16042 p = 1) (hb : d162092 p = 1) : d162170 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d162092 q = 1) : d162165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52326 q ha hb
    | true =>
      simp only [d16037, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d162092 q = 1) : d162166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d162092 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52318 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d162092 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d162092 q = 1) : d162167 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d162092 q = 1) : d162168 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d162092 q = 1) : d162169 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d162169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d162169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16042 q = 1) (hb : d162092 q = 1) : d162170 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16042, d162170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16042, d162170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52328 (p : Pattern) (ha : d16048 p = 1) (hb : d162092 p = 1) : d162176 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d162092 q = 1) : d162171 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52327 q ha hb
    | true =>
      simp only [d16043, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52319 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d162092 q = 1) : d162172 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d162092 q = 1) : d162173 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d162092 q = 1) : d162174 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d162092 q = 1) : d162175 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16048 q = 1) (hb : d162092 q = 1) : d162176 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16048, d162176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16048, d162176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52329 (p : Pattern) (ha : d16051 p = 1) (hb : d162092 p = 1) : d162179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d162092 q = 1) : d162165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52326 q ha hb
    | true =>
      simp only [d16037, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d162092 q = 1) : d162166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d162092 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52318 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d162092 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d162092 q = 1) : d162167 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d162092 q = 1) : d162168 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d162092 q = 1) : d162169 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d162169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d162169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16051 q = 1) (hb : d162092 q = 1) : d162179 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16051, d162179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16051, d162179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52330 (p : Pattern) (ha : d16057 p = 1) (hb : d162092 p = 1) : d162185 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d162092 q = 1) : d162171 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52327 q ha hb
    | true =>
      simp only [d16043, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52319 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d162092 q = 1) : d162172 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d162092 q = 1) : d162173 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d162092 q = 1) : d162174 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d162092 q = 1) : d162175 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16052 q = 1) (hb : d162092 q = 1) : d162180 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d162180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52329 q ha hb
    | true =>
      simp only [d16052, d162180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52320 q ha hb
  have h7 (q : Pattern) (ha : d16053 q = 1) (hb : d162092 q = 1) : d162181 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16054 q = 1) (hb : d162092 q = 1) : d162182 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16054, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16055 q = 1) (hb : d162092 q = 1) : d162183 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16056 q = 1) (hb : d162092 q = 1) : d162184 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16057 q = 1) (hb : d162092 q = 1) : d162185 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16057, d162185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16057, d162185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52331 (p : Pattern) (ha : d16143 p = 1) (hb : d162092 p = 1) : d162250 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d162092 q = 1) : d162171 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52327 q ha hb
    | true =>
      simp only [d16043, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52319 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d162092 q = 1) : d162172 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d162092 q = 1) : d162173 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d162092 q = 1) : d162174 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d162092 q = 1) : d162175 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d162092 q = 1) : d12569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d12569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52319 q ha hb
    | true =>
      simp only [d633, d12569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d162092 q = 1) : d12570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d12570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d12570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d162092 q = 1) : d12571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d12571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d12571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d162092 q = 1) : d12572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d12572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d12572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d162092 q = 1) : d12573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d12573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d12573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16143 q = 1) (hb : d162092 q = 1) : d162250 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16143, d162250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16143, d162250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52332 (p : Pattern) (ha : d514 p = 1) (hb : d162092 p = 1) : d12475 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d162092 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52318 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d162092 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d162092 q = 1) : d12449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d162092 q = 1) : d12450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d162092 q = 1) : d12474 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d12474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d12474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d514 q = 1) (hb : d162092 q = 1) : d12475 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, d12475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, d12475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52333 (p : Pattern) (ha : d524 p = 1) (hb : d162092 p = 1) : d12485 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d162092 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52318 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d162092 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d162092 q = 1) : d12449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d162092 q = 1) : d12483 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d12483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d12483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d162092 q = 1) : d12484 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d12484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d12484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d162092 q = 1) : d12485 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, d12485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, d12485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52334 (p : Pattern) (ha : d16062 p = 1) (hb : d162092 p = 1) : d162190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d162092 q = 1) : d162165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52326 q ha hb
    | true =>
      simp only [d16037, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d162092 q = 1) : d162166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d162092 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52318 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d162092 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d162092 q = 1) : d162167 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d162092 q = 1) : d162168 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d162092 q = 1) : d162189 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d162189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d162189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16062 q = 1) (hb : d162092 q = 1) : d162190 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16062, d162190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16062, d162190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52335 (p : Pattern) (ha : d16069 p = 1) (hb : d162092 p = 1) : d162197 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d162092 q = 1) : d162165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52326 q ha hb
    | true =>
      simp only [d16037, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d162092 q = 1) : d162166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d162092 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52318 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d162092 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d162092 q = 1) : d162167 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d162092 q = 1) : d162195 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d162195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d162195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d162092 q = 1) : d162196 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d162196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d162196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16069 q = 1) (hb : d162092 q = 1) : d162197 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16069, d162197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16069, d162197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52336 (p : Pattern) (ha : d16077 p = 1) (hb : d162092 p = 1) : d162202 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d546 q = 1) : d546 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9458 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51611 q ha hb
    | true =>
      simp only [d9458, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9460 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9460, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16073 q = 1) (hb : d116750 q = 1) : d20992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16073, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16073, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16074 q = 1) (hb : d116750 q = 1) : d20993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16074, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16074, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d16075 q = 1) (hb : d162091 q = 1) : d162201 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, d162091, d162201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16075, d162091, d162201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d16076 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d16077 q = 1) (hb : d162092 q = 1) : d162202 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16077, d162092, d162202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16077, d162092, d162202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro52337 (p : Pattern) (ha : d16081 p = 1) (hb : d162092 p = 1) : d12496 p = 1 := by
  have h0 (q : Pattern) (ha : d12495 q = 1) (hb : d162091 q = 1) : d12495 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16081 q = 1) (hb : d162092 q = 1) : d12496 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16081, d162092, d12496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16081, d162092, d12496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52338 (p : Pattern) (ha : d16087 p = 1) (hb : d162092 p = 1) : d162211 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16078 q = 1) (hb : d162092 q = 1) : d162203 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16078, d162203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52336 q ha hb
    | true =>
      simp only [d16078, d162203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52301 q ha hb
  have h2 (q : Pattern) (ha : d16079 q = 1) (hb : d162092 q = 1) : d162204 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16079, d162204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16079, d162204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16080 q = 1) (hb : d162092 q = 1) : d162205 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16080, d162205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16080, d162205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16082 q = 1) (hb : d162092 q = 1) : d162206 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16082, d162206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52301 q ha hb
    | true =>
      simp only [d16082, d162206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52337 q ha hb
  have h5 (q : Pattern) (ha : d16083 q = 1) (hb : d162092 q = 1) : d162207 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16083, d162207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16083, d162207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16084 q = 1) (hb : d162092 q = 1) : d162208 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16084, d162208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16084, d162208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16085 q = 1) (hb : d162092 q = 1) : d162209 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16085, d162209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16085, d162209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15967 q = 1) (hb : d162092 q = 1) : d162096 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d162096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52301 q ha hb
    | true =>
      simp only [d15967, d162096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52283 q ha hb
  have h9 (q : Pattern) (ha : d15968 q = 1) (hb : d162092 q = 1) : d162097 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d162097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d162097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15969 q = 1) (hb : d162092 q = 1) : d162098 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d162098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d162098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d162092 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d145 q = 1) (hb : d162092 q = 1) : d4819 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52283 q ha hb
    | true =>
      simp only [d145, d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146 q = 1) (hb : d162092 q = 1) : d4820 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147 q = 1) (hb : d162092 q = 1) : d4821 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15970 q = 1) (hb : d162092 q = 1) : d162099 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d162099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15970, d162099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16086 q = 1) (hb : d162092 q = 1) : d162210 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16086, d162210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16086, d162210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16087 q = 1) (hb : d162092 q = 1) : d162211 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16087, d162211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16087, d162211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro52339 (p : Pattern) (ha : d16093 p = 1) (hb : d162092 p = 1) : d162217 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16088 q = 1) (hb : d162092 q = 1) : d162212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16088, d162212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52338 q ha hb
    | true =>
      simp only [d16088, d162212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16089 q = 1) (hb : d162092 q = 1) : d162213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16089, d162213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16089, d162213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d162092 q = 1) : d162165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52326 q ha hb
    | true =>
      simp only [d16037, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d162092 q = 1) : d162166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16090 q = 1) (hb : d162092 q = 1) : d162214 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16090, d162214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16090, d162214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16091 q = 1) (hb : d162092 q = 1) : d162215 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16091, d162215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16091, d162215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16092 q = 1) (hb : d162092 q = 1) : d162216 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16092, d162216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16092, d162216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16093 q = 1) (hb : d162092 q = 1) : d162217 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16093, d162217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16093, d162217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52340 (p : Pattern) (ha : d16114 p = 1) (hb : d162092 p = 1) : d162223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d162092 q = 1) : d162165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52326 q ha hb
    | true =>
      simp only [d16037, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d162092 q = 1) : d162166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d162092 q = 1) : d162220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d162220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d162220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d162092 q = 1) : d162221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d162221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d162221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d162092 q = 1) : d162222 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d162222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d162222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16114 q = 1) (hb : d162092 q = 1) : d162223 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16114, d162223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16114, d162223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52341 (p : Pattern) (ha : d128234 p = 1) (hb : d162092 p = 1) : d162229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d162092 q = 1) : d162191 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d162191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52334 q ha hb
    | true =>
      simp only [d16063, d162191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52332 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d162092 q = 1) : d162192 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d162192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d162192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d162092 q = 1) : d162193 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d162193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d162193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d162092 q = 1) : d162194 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d162194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d162194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d162092 q = 1) : d162198 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d162198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52335 q ha hb
    | true =>
      simp only [d16070, d162198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52333 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d162092 q = 1) : d162199 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d162199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d162199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d162092 q = 1) : d162200 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d162200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d162200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16094 q = 1) (hb : d162092 q = 1) : d162218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16094, d162218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52339 q ha hb
    | true =>
      simp only [d16094, d162218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52327 q ha hb
  have h9 (q : Pattern) (ha : d128230 q = 1) (hb : d162092 q = 1) : d162219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128230, d162219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128230, d162219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d162092 q = 1) : d162224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d162224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52340 q ha hb
    | true =>
      simp only [d16115, d162224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d162092 q = 1) : d162225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d162225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d162225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128231 q = 1) (hb : d162092 q = 1) : d162226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128231, d162226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128231, d162226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128232 q = 1) (hb : d162092 q = 1) : d162227 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128232, d162227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128232, d162227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128233 q = 1) (hb : d162092 q = 1) : d162228 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128233, d162228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128233, d162228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128234 q = 1) (hb : d162092 q = 1) : d162229 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128234, d162229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128234, d162229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro52342 (p : Pattern) (ha : d610 p = 1) (hb : d162092 p = 1) : d12545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d162092 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52318 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d162092 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d162092 q = 1) : d12449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d162092 q = 1) : d12450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d162092 q = 1) : d12474 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d12474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d12474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d610 q = 1) (hb : d162092 q = 1) : d12545 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, d12545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d610, d12545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52343 (p : Pattern) (ha : d616 p = 1) (hb : d162092 p = 1) : d12551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d162092 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52318 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d162092 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d162092 q = 1) : d12449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d162092 q = 1) : d12483 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d12483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d12483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d162092 q = 1) : d12484 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d12484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d12484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d616 q = 1) (hb : d162092 q = 1) : d12551 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, d12551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d616, d12551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52344 (p : Pattern) (ha : d16121 p = 1) (hb : d162092 p = 1) : d162230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d162092 q = 1) : d162165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52326 q ha hb
    | true =>
      simp only [d16037, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d162092 q = 1) : d162166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d162092 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52318 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d162092 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d162092 q = 1) : d162167 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d162092 q = 1) : d162168 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d162092 q = 1) : d162189 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d162189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d162189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16121 q = 1) (hb : d162092 q = 1) : d162230 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16121, d162230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16121, d162230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52345 (p : Pattern) (ha : d16126 p = 1) (hb : d162092 p = 1) : d162235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d162092 q = 1) : d162165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52326 q ha hb
    | true =>
      simp only [d16037, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d162092 q = 1) : d162166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d162092 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52318 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d162092 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d162092 q = 1) : d162167 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d162092 q = 1) : d162195 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d162195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d162195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d162092 q = 1) : d162196 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d162196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d162196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16126 q = 1) (hb : d162092 q = 1) : d162235 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16126, d162235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16126, d162235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52346 (p : Pattern) (ha : d16130 p = 1) (hb : d162092 p = 1) : d162239 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16088 q = 1) (hb : d162092 q = 1) : d162212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16088, d162212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52338 q ha hb
    | true =>
      simp only [d16088, d162212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16089 q = 1) (hb : d162092 q = 1) : d162213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16089, d162213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16089, d162213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d162092 q = 1) : d162165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52326 q ha hb
    | true =>
      simp only [d16037, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d162092 q = 1) : d162166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16090 q = 1) (hb : d162092 q = 1) : d162214 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16090, d162214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16090, d162214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16091 q = 1) (hb : d162092 q = 1) : d162215 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16091, d162215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16091, d162215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16092 q = 1) (hb : d162092 q = 1) : d162216 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16092, d162216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16092, d162216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16130 q = 1) (hb : d162092 q = 1) : d162239 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16130, d162239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16130, d162239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52347 (p : Pattern) (ha : d16135 p = 1) (hb : d162092 p = 1) : d162242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d162092 q = 1) : d162165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52326 q ha hb
    | true =>
      simp only [d16037, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d162092 q = 1) : d162166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d162092 q = 1) : d162220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d162220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d162220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d162092 q = 1) : d162221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d162221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d162221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d162092 q = 1) : d162222 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d162222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d162222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16135 q = 1) (hb : d162092 q = 1) : d162242 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16135, d162242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16135, d162242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52348 (p : Pattern) (ha : d128239 p = 1) (hb : d162092 p = 1) : d162248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d162092 q = 1) : d162191 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d162191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52334 q ha hb
    | true =>
      simp only [d16063, d162191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52332 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d162092 q = 1) : d162192 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d162192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d162192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d162092 q = 1) : d162193 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d162193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d162193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d162092 q = 1) : d162194 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d162194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d162194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d162092 q = 1) : d162198 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d162198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52335 q ha hb
    | true =>
      simp only [d16070, d162198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52333 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d162092 q = 1) : d162199 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d162199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d162199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d162092 q = 1) : d162200 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d162200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d162200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16094 q = 1) (hb : d162092 q = 1) : d162218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16094, d162218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52339 q ha hb
    | true =>
      simp only [d16094, d162218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52327 q ha hb
  have h9 (q : Pattern) (ha : d128230 q = 1) (hb : d162092 q = 1) : d162219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128230, d162219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128230, d162219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d162092 q = 1) : d162224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d162224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52340 q ha hb
    | true =>
      simp only [d16115, d162224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d162092 q = 1) : d162225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d162225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d162225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128231 q = 1) (hb : d162092 q = 1) : d162226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128231, d162226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128231, d162226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128232 q = 1) (hb : d162092 q = 1) : d162227 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128232, d162227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128232, d162227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128233 q = 1) (hb : d162092 q = 1) : d162228 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128233, d162228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128233, d162228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16122 q = 1) (hb : d162092 q = 1) : d162231 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16122, d162231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52344 q ha hb
    | true =>
      simp only [d16122, d162231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52342 q ha hb
  have h16 (q : Pattern) (ha : d16123 q = 1) (hb : d162092 q = 1) : d162232 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16123, d162232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16123, d162232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16124 q = 1) (hb : d162092 q = 1) : d162233 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16124, d162233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16124, d162233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16125 q = 1) (hb : d162092 q = 1) : d162234 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16125, d162234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16125, d162234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16127 q = 1) (hb : d162092 q = 1) : d162236 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16127, d162236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52345 q ha hb
    | true =>
      simp only [d16127, d162236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52343 q ha hb
  have h20 (q : Pattern) (ha : d16128 q = 1) (hb : d162092 q = 1) : d162237 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16128, d162237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16128, d162237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16129 q = 1) (hb : d162092 q = 1) : d162238 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16129, d162238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16129, d162238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16131 q = 1) (hb : d162092 q = 1) : d162240 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16131, d162240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52346 q ha hb
    | true =>
      simp only [d16131, d162240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52329 q ha hb
  have h23 (q : Pattern) (ha : d128235 q = 1) (hb : d162092 q = 1) : d162241 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128235, d162241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128235, d162241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16136 q = 1) (hb : d162092 q = 1) : d162243 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d162243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52347 q ha hb
    | true =>
      simp only [d16136, d162243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16137 q = 1) (hb : d162092 q = 1) : d162244 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d162244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16137, d162244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128236 q = 1) (hb : d162092 q = 1) : d162245 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128236, d162245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128236, d162245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128237 q = 1) (hb : d162092 q = 1) : d162246 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128237, d162246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128237, d162246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128238 q = 1) (hb : d162092 q = 1) : d162247 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128238, d162247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128238, d162247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128239 q = 1) (hb : d162092 q = 1) : d162248 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128239, d162248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128239, d162248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro52349 (p : Pattern) (ha : d128246 p = 1) (hb : d162092 p = 1) : d162257 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16131 q = 1) (hb : d162092 q = 1) : d162240 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16131, d162240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52346 q ha hb
    | true =>
      simp only [d16131, d162240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52329 q ha hb
  have h2 (q : Pattern) (ha : d128235 q = 1) (hb : d162092 q = 1) : d162241 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128235, d162241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128235, d162241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16136 q = 1) (hb : d162092 q = 1) : d162243 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d162243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52347 q ha hb
    | true =>
      simp only [d16136, d162243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16137 q = 1) (hb : d162092 q = 1) : d162244 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d162244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16137, d162244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128236 q = 1) (hb : d162092 q = 1) : d162245 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128236, d162245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128236, d162245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128244 q = 1) (hb : d162092 q = 1) : d162255 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128244, d162255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128244, d162255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128245 q = 1) (hb : d162092 q = 1) : d162256 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128245, d162256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128245, d162256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128246 q = 1) (hb : d162092 q = 1) : d162257 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128246, d162257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128246, d162257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52350 (p : Pattern) (ha : d16162 p = 1) (hb : d162092 p = 1) : d162264 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d662 q = 1) : d662 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16156 q = 1) (hb : d116750 q = 1) : d21071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16156, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51611 q ha hb
  have h3 (q : Pattern) (ha : d9458 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51611 q ha hb
    | true =>
      simp only [d9458, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16157 q = 1) (hb : d116750 q = 1) : d21072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16157, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9460 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9460, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d16158 q = 1) (hb : d116750 q = 1) : d21073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16158, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16158, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16159 q = 1) (hb : d116750 q = 1) : d21074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16159, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16159, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d16160 q = 1) (hb : d162091 q = 1) : d162263 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16160, d162091, d162263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16160, d162091, d162263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16161 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16162 q = 1) (hb : d162092 q = 1) : d162264 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16162, d162092, d162264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16162, d162092, d162264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro52351 (p : Pattern) (ha : d16166 p = 1) (hb : d162092 p = 1) : d12604 p = 1 := by
  have h0 (q : Pattern) (ha : d12603 q = 1) (hb : d162091 q = 1) : d12603 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16166 q = 1) (hb : d162092 q = 1) : d12604 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16166, d162092, d12604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16166, d162092, d12604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52352 (p : Pattern) (ha : d16172 p = 1) (hb : d162092 p = 1) : d162273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16163 q = 1) (hb : d162092 q = 1) : d162265 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16163, d162265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52350 q ha hb
    | true =>
      simp only [d16163, d162265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52312 q ha hb
  have h2 (q : Pattern) (ha : d16164 q = 1) (hb : d162092 q = 1) : d162266 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16164, d162266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16164, d162266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16165 q = 1) (hb : d162092 q = 1) : d162267 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16165, d162267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16165, d162267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16167 q = 1) (hb : d162092 q = 1) : d162268 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16167, d162268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52312 q ha hb
    | true =>
      simp only [d16167, d162268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52351 q ha hb
  have h5 (q : Pattern) (ha : d16168 q = 1) (hb : d162092 q = 1) : d162269 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16168, d162269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16168, d162269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16169 q = 1) (hb : d162092 q = 1) : d162270 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16169, d162270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16169, d162270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16170 q = 1) (hb : d162092 q = 1) : d162271 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16170, d162271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16170, d162271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16005 q = 1) (hb : d162092 q = 1) : d162133 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d162133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52312 q ha hb
    | true =>
      simp only [d16005, d162133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52287 q ha hb
  have h9 (q : Pattern) (ha : d16006 q = 1) (hb : d162092 q = 1) : d162134 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d162134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d162134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16007 q = 1) (hb : d162092 q = 1) : d162135 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d162135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d162135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d162092 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d232 q = 1) (hb : d162092 q = 1) : d6079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52287 q ha hb
    | true =>
      simp only [d232, d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d233 q = 1) (hb : d162092 q = 1) : d6080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234 q = 1) (hb : d162092 q = 1) : d6081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16008 q = 1) (hb : d162092 q = 1) : d162136 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d162136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16008, d162136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16171 q = 1) (hb : d162092 q = 1) : d162272 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16171, d162272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16171, d162272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16172 q = 1) (hb : d162092 q = 1) : d162273 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16172, d162273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16172, d162273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro52353 (p : Pattern) (ha : d16176 p = 1) (hb : d162092 p = 1) : d162277 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d162092 q = 1) : d162133 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d162133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52312 q ha hb
    | true =>
      simp only [d16005, d162133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52287 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d162092 q = 1) : d162134 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d162134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d162134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d162092 q = 1) : d162135 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d162135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d162135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d162092 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d162092 q = 1) : d6079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52287 q ha hb
    | true =>
      simp only [d232, d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d162092 q = 1) : d6080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d162092 q = 1) : d6081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d162092 q = 1) : d162136 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d162136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d162136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d673 q = 1) (hb : d162092 q = 1) : d6082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d6082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d673, d6082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16175 q = 1) (hb : d162092 q = 1) : d162276 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16175, d162276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16175, d162276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16176 q = 1) (hb : d162092 q = 1) : d162277 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16176, d162277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16176, d162277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro52354 (p : Pattern) (ha : d16182 p = 1) (hb : d162092 p = 1) : d162283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16173 q = 1) (hb : d162092 q = 1) : d162274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16173, d162274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52352 q ha hb
    | true =>
      simp only [d16173, d162274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16174 q = 1) (hb : d162092 q = 1) : d162275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16174, d162275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16174, d162275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16177 q = 1) (hb : d162092 q = 1) : d162278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d162278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52353 q ha hb
    | true =>
      simp only [d16177, d162278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16178 q = 1) (hb : d162092 q = 1) : d162279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d162279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d162279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16179 q = 1) (hb : d162092 q = 1) : d162280 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16179, d162280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16179, d162280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16180 q = 1) (hb : d162092 q = 1) : d162281 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16180, d162281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16180, d162281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16181 q = 1) (hb : d162092 q = 1) : d162282 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16181, d162282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16181, d162282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16182 q = 1) (hb : d162092 q = 1) : d162283 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16182, d162283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16182, d162283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52355 (p : Pattern) (ha : d16186 p = 1) (hb : d162092 p = 1) : d162287 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d162092 q = 1) : d162278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d162278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52353 q ha hb
    | true =>
      simp only [d16177, d162278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d162092 q = 1) : d162279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d162279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d162279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d162092 q = 1) : d12623 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d12623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52323 q ha hb
    | true =>
      simp only [d684, d12623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d162092 q = 1) : d12624 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d12624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d12624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16183 q = 1) (hb : d162092 q = 1) : d162284 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16183, d162284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16183, d162284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16184 q = 1) (hb : d162092 q = 1) : d162285 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16184, d162285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16184, d162285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16185 q = 1) (hb : d162092 q = 1) : d162286 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16185, d162286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16185, d162286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16186 q = 1) (hb : d162092 q = 1) : d162287 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16186, d162287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16186, d162287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52356 (p : Pattern) (ha : d16207 p = 1) (hb : d162092 p = 1) : d162293 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d162092 q = 1) : d162278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d162278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52353 q ha hb
    | true =>
      simp only [d16177, d162278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d162092 q = 1) : d162279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d162279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d162279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16204 q = 1) (hb : d162092 q = 1) : d162290 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16204, d162290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16204, d162290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16205 q = 1) (hb : d162092 q = 1) : d162291 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16205, d162291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16205, d162291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16206 q = 1) (hb : d162092 q = 1) : d162292 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16206, d162292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16206, d162292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16207 q = 1) (hb : d162092 q = 1) : d162293 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16207, d162293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16207, d162293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52357 (p : Pattern) (ha : d128256 p = 1) (hb : d162092 p = 1) : d162299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16187 q = 1) (hb : d162092 q = 1) : d162288 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16187, d162288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52354 q ha hb
    | true =>
      simp only [d16187, d162288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52355 q ha hb
  have h2 (q : Pattern) (ha : d128252 q = 1) (hb : d162092 q = 1) : d162289 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128252, d162289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128252, d162289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16208 q = 1) (hb : d162092 q = 1) : d162294 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16208, d162294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52356 q ha hb
    | true =>
      simp only [d16208, d162294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16209 q = 1) (hb : d162092 q = 1) : d162295 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16209, d162295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16209, d162295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128253 q = 1) (hb : d162092 q = 1) : d162296 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128253, d162296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128253, d162296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128254 q = 1) (hb : d162092 q = 1) : d162297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128254, d162297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128254, d162297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128255 q = 1) (hb : d162092 q = 1) : d162298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128255, d162298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128255, d162298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128256 q = 1) (hb : d162092 q = 1) : d162299 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128256, d162299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128256, d162299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52358 (p : Pattern) (ha : d128262 p = 1) (hb : d162092 p = 1) : d162305 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16049 q = 1) (hb : d162092 q = 1) : d162177 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16049, d162177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16049, d162177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52328 q ha hb
  have h2 (q : Pattern) (ha : d16050 q = 1) (hb : d162092 q = 1) : d162178 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16050, d162178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16050, d162178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16058 q = 1) (hb : d162092 q = 1) : d162186 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, d162186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52328 q ha hb
    | true =>
      simp only [d16058, d162186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52330 q ha hb
  have h4 (q : Pattern) (ha : d16059 q = 1) (hb : d162092 q = 1) : d162187 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, d162187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16059, d162187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16060 q = 1) (hb : d162092 q = 1) : d162188 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16060, d162188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16060, d162188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128240 q = 1) (hb : d162092 q = 1) : d162249 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128240, d162249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52341 q ha hb
    | true =>
      simp only [d128240, d162249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52348 q ha hb
  have h7 (q : Pattern) (ha : d16144 q = 1) (hb : d162092 q = 1) : d162251 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16144, d162251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52331 q ha hb
    | true =>
      simp only [d16144, d162251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52321 q ha hb
  have h8 (q : Pattern) (ha : d128241 q = 1) (hb : d162092 q = 1) : d162252 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128241, d162252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128241, d162252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128242 q = 1) (hb : d162092 q = 1) : d162253 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128242, d162253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128242, d162253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128243 q = 1) (hb : d162092 q = 1) : d162254 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128243, d162254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128243, d162254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128247 q = 1) (hb : d162092 q = 1) : d162258 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128247, d162258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128247, d162258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52349 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d162092 q = 1) : d12590 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d12590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d12590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52322 q ha hb
  have h13 (q : Pattern) (ha : d128248 q = 1) (hb : d162092 q = 1) : d162259 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128248, d162259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128248, d162259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128249 q = 1) (hb : d162092 q = 1) : d162260 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128249, d162260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128249, d162260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128250 q = 1) (hb : d162092 q = 1) : d162261 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128250, d162261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128250, d162261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128251 q = 1) (hb : d162092 q = 1) : d162262 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128251, d162262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128251, d162262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128257 q = 1) (hb : d162092 q = 1) : d162300 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128257, d162300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128257, d162300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52357 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d162092 q = 1) : d12675 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d12675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d12675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52325 q ha hb
  have h19 (q : Pattern) (ha : d128258 q = 1) (hb : d162092 q = 1) : d162301 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128258, d162301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128258, d162301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128259 q = 1) (hb : d162092 q = 1) : d162302 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128259, d162302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128259, d162302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128260 q = 1) (hb : d162092 q = 1) : d162303 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128260, d162303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128260, d162303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128261 q = 1) (hb : d162092 q = 1) : d162304 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128261, d162304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128261, d162304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128262 q = 1) (hb : d162092 q = 1) : d162305 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128262, d162305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128262, d162305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro52359 (p : Pattern) (ha : d128268 p = 1) (hb : d162092 p = 1) : d162311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128263 q = 1) (hb : d162092 q = 1) : d162306 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128263, d162306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128263, d162306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52358 q ha hb
  have h2 (q : Pattern) (ha : d128264 q = 1) (hb : d162092 q = 1) : d162307 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128264, d162307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128264, d162307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128265 q = 1) (hb : d162092 q = 1) : d162308 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128265, d162308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128265, d162308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128266 q = 1) (hb : d162092 q = 1) : d162309 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128266, d162309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128266, d162309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128267 q = 1) (hb : d162092 q = 1) : d162310 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128267, d162310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128267, d162310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128268 q = 1) (hb : d162092 q = 1) : d162311 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128268, d162311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128268, d162311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52360 (p : Pattern) (ha : d758 p = 1) (hb : d162092 p = 1) : d4913 p = 1 := by
  have h0 (q : Pattern) (ha : d755 q = 1) (hb : d162091 q = 1) : d755 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d757 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d758 q = 1) (hb : d162092 q = 1) : d4913 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d758, d162092, d4913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d758, d162092, d4913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52361 (p : Pattern) (ha : d773 p = 1) (hb : d162092 p = 1) : d12697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d762 q = 1) (hb : d162092 q = 1) : d762 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d763 q = 1) (hb : d162092 q = 1) : d4914 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d4914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52360 q ha hb
    | true =>
      simp only [d763, d4914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d764 q = 1) (hb : d162092 q = 1) : d4915 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d4915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d4915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d765 q = 1) (hb : d162092 q = 1) : d4916 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d4916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d4916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d767 q = 1) (hb : d162092 q = 1) : d4917 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d4917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d767, d4917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d772 q = 1) (hb : d162092 q = 1) : d12696 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, d12696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d772, d12696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d773 q = 1) (hb : d162092 q = 1) : d12697 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d773, d12697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d773, d12697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro52362 (p : Pattern) (ha : d783 p = 1) (hb : d162092 p = 1) : d12707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d162092 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52361 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d162092 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d162092 q = 1) : d12704 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d162092 q = 1) : d12705 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d162092 q = 1) : d12706 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d12706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d12706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d783 q = 1) (hb : d162092 q = 1) : d12707 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, d12707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, d12707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52363 (p : Pattern) (ha : d793 p = 1) (hb : d162092 p = 1) : d12717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d162092 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52361 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d162092 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d162092 q = 1) : d12704 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d162092 q = 1) : d12705 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d162092 q = 1) : d12706 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d12706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d12706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d793 q = 1) (hb : d162092 q = 1) : d12717 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, d12717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d793, d12717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52364 (p : Pattern) (ha : d950 p = 1) (hb : d162092 p = 1) : d12839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d162092 q = 1) : d12828 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d12828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52362 q ha hb
    | true =>
      simp only [d939, d12828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d162092 q = 1) : d12829 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d12829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d12829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d162092 q = 1) : d12830 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d12830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, d12830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d162092 q = 1) : d12831 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d12831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d12831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d162092 q = 1) : d12832 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d12832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d12832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d945 q = 1) (hb : d162092 q = 1) : d12834 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d12834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52363 q ha hb
    | true =>
      simp only [d945, d12834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d946 q = 1) (hb : d162092 q = 1) : d12835 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d12835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d12835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d947 q = 1) (hb : d162092 q = 1) : d12836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d12836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d947, d12836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d948 q = 1) (hb : d162092 q = 1) : d12837 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d12837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d12837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d949 q = 1) (hb : d162092 q = 1) : d12838 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d12838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d12838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d950 q = 1) (hb : d162092 q = 1) : d12839 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, d12839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d950, d12839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52365 (p : Pattern) (ha : d959 p = 1) (hb : d162092 p = 1) : d12848 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d945 q = 1) (hb : d162092 q = 1) : d12834 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d12834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52363 q ha hb
    | true =>
      simp only [d945, d12834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d946 q = 1) (hb : d162092 q = 1) : d12835 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d12835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d12835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d162092 q = 1) : d12836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d12836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d947, d12836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d162092 q = 1) : d12837 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d12837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d12837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d162092 q = 1) : d12838 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d12838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d12838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d162092 q = 1) : d12848 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, d12848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, d12848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52366 (p : Pattern) (ha : d981 p = 1) (hb : d162092 p = 1) : d6210 p = 1 := by
  have h0 (q : Pattern) (ha : d975 q = 1) (hb : d162091 q = 1) : d975 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d981 q = 1) (hb : d162092 q = 1) : d6210 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d981, d162092, d6210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d981, d162092, d6210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52367 (p : Pattern) (ha : d1005 p = 1) (hb : d162092 p = 1) : d12885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d986 q = 1) (hb : d162092 q = 1) : d986 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d987 q = 1) (hb : d162092 q = 1) : d6211 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d6211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52366 q ha hb
    | true =>
      simp only [d987, d6211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d988 q = 1) (hb : d162092 q = 1) : d6212 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d6212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d6212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d989 q = 1) (hb : d162092 q = 1) : d6213 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d6213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d6213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d995 q = 1) (hb : d162092 q = 1) : d6214 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d6214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d995, d6214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1004 q = 1) (hb : d162092 q = 1) : d12884 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d12884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1004, d12884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1005 q = 1) (hb : d162092 q = 1) : d12885 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, d12885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1005, d12885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro52368 (p : Pattern) (ha : d1063 p = 1) (hb : d162092 p = 1) : d12935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d162092 q = 1) : d12886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d12886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52367 q ha hb
    | true =>
      simp only [d1006, d12886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d162092 q = 1) : d12887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d12887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d12887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1060 q = 1) (hb : d162092 q = 1) : d12932 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d12932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, d12932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d162092 q = 1) : d12933 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, d12933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1061, d12933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d162092 q = 1) : d12934 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, d12934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, d12934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d162092 q = 1) : d12935 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, d12935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, d12935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52369 (p : Pattern) (ha : d1069 p = 1) (hb : d162092 p = 1) : d12941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d162092 q = 1) : d12936 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, d12936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52368 q ha hb
    | true =>
      simp only [d1064, d12936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d162092 q = 1) : d12937 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d12937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, d12937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d162092 q = 1) : d12938 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d12938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, d12938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d162092 q = 1) : d12939 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, d12939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, d12939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d162092 q = 1) : d12940 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, d12940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, d12940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d162092 q = 1) : d12941 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, d12941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, d12941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52370 (p : Pattern) (ha : d16227 p = 1) (hb : d162092 p = 1) : d162202 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d546 q = 1) : d546 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9458 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51611 q ha hb
    | true =>
      simp only [d9458, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9460 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9460, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16073 q = 1) (hb : d116750 q = 1) : d20992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16073, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16073, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16074 q = 1) (hb : d116750 q = 1) : d20993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16074, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16074, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d16075 q = 1) (hb : d162091 q = 1) : d162201 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, d162091, d162201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16075, d162091, d162201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d12750 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d16227 q = 1) (hb : d162092 q = 1) : d162202 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16227, d162092, d162202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16227, d162092, d162202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro52371 (p : Pattern) (ha : d16233 p = 1) (hb : d162092 p = 1) : d162315 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16228 q = 1) (hb : d162092 q = 1) : d162203 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d162203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52370 q ha hb
    | true =>
      simp only [d16228, d162203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52360 q ha hb
  have h2 (q : Pattern) (ha : d16229 q = 1) (hb : d162092 q = 1) : d162204 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16229, d162204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16229, d162204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16230 q = 1) (hb : d162092 q = 1) : d162205 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16230, d162205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16230, d162205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d762 q = 1) (hb : d162092 q = 1) : d762 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d763 q = 1) (hb : d162092 q = 1) : d4914 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d4914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52360 q ha hb
    | true =>
      simp only [d763, d4914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d764 q = 1) (hb : d162092 q = 1) : d4915 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d4915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d4915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d765 q = 1) (hb : d162092 q = 1) : d4916 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d4916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d4916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16231 q = 1) (hb : d162092 q = 1) : d162313 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16231, d162313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16231, d162313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d767 q = 1) (hb : d162092 q = 1) : d4917 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d4917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d767, d4917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16232 q = 1) (hb : d162092 q = 1) : d162314 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16232, d162314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16232, d162314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16233 q = 1) (hb : d162092 q = 1) : d162315 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16233, d162315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16233, d162315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro52372 (p : Pattern) (ha : d16239 p = 1) (hb : d162092 p = 1) : d162321 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d162092 q = 1) : d162316 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52371 q ha hb
    | true =>
      simp only [d16234, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d162092 q = 1) : d162317 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d162092 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52361 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d162092 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d162092 q = 1) : d162318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d162092 q = 1) : d162319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16238 q = 1) (hb : d162092 q = 1) : d162320 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16238, d162320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16238, d162320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16239 q = 1) (hb : d162092 q = 1) : d162321 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16239, d162321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16239, d162321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52373 (p : Pattern) (ha : d16245 p = 1) (hb : d162092 p = 1) : d162327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d162092 q = 1) : d162322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52372 q ha hb
    | true =>
      simp only [d16240, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52362 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d162092 q = 1) : d162323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d162092 q = 1) : d162324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d162092 q = 1) : d162325 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d162092 q = 1) : d162326 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16245 q = 1) (hb : d162092 q = 1) : d162327 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16245, d162327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16245, d162327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52374 (p : Pattern) (ha : d16248 p = 1) (hb : d162092 p = 1) : d162330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d162092 q = 1) : d162316 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52371 q ha hb
    | true =>
      simp only [d16234, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d162092 q = 1) : d162317 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d162092 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52361 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d162092 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d162092 q = 1) : d162318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d162092 q = 1) : d162319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16238 q = 1) (hb : d162092 q = 1) : d162320 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16238, d162320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16238, d162320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16248 q = 1) (hb : d162092 q = 1) : d162330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16248, d162330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16248, d162330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52375 (p : Pattern) (ha : d16254 p = 1) (hb : d162092 p = 1) : d162336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d162092 q = 1) : d162322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52372 q ha hb
    | true =>
      simp only [d16240, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52362 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d162092 q = 1) : d162323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d162092 q = 1) : d162324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d162092 q = 1) : d162325 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d162092 q = 1) : d162326 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16249 q = 1) (hb : d162092 q = 1) : d162331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16249, d162331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52374 q ha hb
    | true =>
      simp only [d16249, d162331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52363 q ha hb
  have h7 (q : Pattern) (ha : d16250 q = 1) (hb : d162092 q = 1) : d162332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16250, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16250, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16251 q = 1) (hb : d162092 q = 1) : d162333 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16251, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16251, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16252 q = 1) (hb : d162092 q = 1) : d162334 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16252, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16252, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16253 q = 1) (hb : d162092 q = 1) : d162335 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16253, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16253, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16254 q = 1) (hb : d162092 q = 1) : d162336 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16254, d162336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16254, d162336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52376 (p : Pattern) (ha : d16343 p = 1) (hb : d162092 p = 1) : d162401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d162092 q = 1) : d162322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52372 q ha hb
    | true =>
      simp only [d16240, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52362 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d162092 q = 1) : d162323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d162092 q = 1) : d162324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d162092 q = 1) : d162325 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d162092 q = 1) : d162326 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d162092 q = 1) : d12828 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d12828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52362 q ha hb
    | true =>
      simp only [d939, d12828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d162092 q = 1) : d12829 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d12829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d12829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d162092 q = 1) : d12830 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d12830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d12830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d162092 q = 1) : d12831 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d12831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d12831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d162092 q = 1) : d12832 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d12832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d12832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16343 q = 1) (hb : d162092 q = 1) : d162401 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16343, d162401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16343, d162401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52377 (p : Pattern) (ha : d806 p = 1) (hb : d162092 p = 1) : d12730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d162092 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52361 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d162092 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d162092 q = 1) : d12704 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d162092 q = 1) : d12705 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d162092 q = 1) : d12729 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d12729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d12729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d806 q = 1) (hb : d162092 q = 1) : d12730 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d12730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d12730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52378 (p : Pattern) (ha : d816 p = 1) (hb : d162092 p = 1) : d12740 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d162092 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52361 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d162092 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d162092 q = 1) : d12704 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d162092 q = 1) : d12738 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d12738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d12738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d162092 q = 1) : d12739 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d12739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d12739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d162092 q = 1) : d12740 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d12740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d12740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52379 (p : Pattern) (ha : d16259 p = 1) (hb : d162092 p = 1) : d162341 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d162092 q = 1) : d162316 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52371 q ha hb
    | true =>
      simp only [d16234, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d162092 q = 1) : d162317 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d162092 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52361 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d162092 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d162092 q = 1) : d162318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d162092 q = 1) : d162319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16258 q = 1) (hb : d162092 q = 1) : d162340 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16258, d162340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16258, d162340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16259 q = 1) (hb : d162092 q = 1) : d162341 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16259, d162341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16259, d162341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52380 (p : Pattern) (ha : d16266 p = 1) (hb : d162092 p = 1) : d162348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d162092 q = 1) : d162316 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52371 q ha hb
    | true =>
      simp only [d16234, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d162092 q = 1) : d162317 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d162092 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52361 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d162092 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d162092 q = 1) : d162318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16264 q = 1) (hb : d162092 q = 1) : d162346 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16264, d162346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16264, d162346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16265 q = 1) (hb : d162092 q = 1) : d162347 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16265, d162347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16265, d162347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16266 q = 1) (hb : d162092 q = 1) : d162348 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16266, d162348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16266, d162348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52381 (p : Pattern) (ha : d16274 p = 1) (hb : d162092 p = 1) : d162353 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d837 q = 1) : d837 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9587 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51657 q ha hb
    | true =>
      simp only [d9587, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9589 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9589, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9589, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16270 q = 1) (hb : d116750 q = 1) : d21185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16270, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16270, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16271 q = 1) (hb : d116750 q = 1) : d21186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16271, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16271, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d16272 q = 1) (hb : d162091 q = 1) : d162352 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16272, d162091, d162352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16272, d162091, d162352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d16273 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d16274 q = 1) (hb : d162092 q = 1) : d162353 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16274, d162092, d162353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16274, d162092, d162353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro52382 (p : Pattern) (ha : d16278 p = 1) (hb : d162092 p = 1) : d12751 p = 1 := by
  have h0 (q : Pattern) (ha : d12750 q = 1) (hb : d162091 q = 1) : d12750 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d757 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16278 q = 1) (hb : d162092 q = 1) : d12751 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16278, d162092, d12751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16278, d162092, d12751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52383 (p : Pattern) (ha : d16284 p = 1) (hb : d162092 p = 1) : d162362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16275 q = 1) (hb : d162092 q = 1) : d162354 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16275, d162354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52381 q ha hb
    | true =>
      simp only [d16275, d162354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52370 q ha hb
  have h2 (q : Pattern) (ha : d16276 q = 1) (hb : d162092 q = 1) : d162355 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16276, d162355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16276, d162355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16277 q = 1) (hb : d162092 q = 1) : d162356 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16277, d162356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16277, d162356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16279 q = 1) (hb : d162092 q = 1) : d162357 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16279, d162357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52370 q ha hb
    | true =>
      simp only [d16279, d162357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52382 q ha hb
  have h5 (q : Pattern) (ha : d16280 q = 1) (hb : d162092 q = 1) : d162358 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16280, d162358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16280, d162358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16281 q = 1) (hb : d162092 q = 1) : d162359 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16281, d162359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16281, d162359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16282 q = 1) (hb : d162092 q = 1) : d162360 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16282, d162360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16282, d162360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16228 q = 1) (hb : d162092 q = 1) : d162203 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d162203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52370 q ha hb
    | true =>
      simp only [d16228, d162203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52360 q ha hb
  have h9 (q : Pattern) (ha : d16229 q = 1) (hb : d162092 q = 1) : d162204 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16229, d162204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16229, d162204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16230 q = 1) (hb : d162092 q = 1) : d162205 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16230, d162205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16230, d162205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d762 q = 1) (hb : d162092 q = 1) : d762 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d763 q = 1) (hb : d162092 q = 1) : d4914 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d4914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52360 q ha hb
    | true =>
      simp only [d763, d4914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d764 q = 1) (hb : d162092 q = 1) : d4915 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d4915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d4915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d765 q = 1) (hb : d162092 q = 1) : d4916 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d4916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d4916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16231 q = 1) (hb : d162092 q = 1) : d162313 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16231, d162313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16231, d162313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16283 q = 1) (hb : d162092 q = 1) : d162361 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16283, d162361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16283, d162361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16284 q = 1) (hb : d162092 q = 1) : d162362 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16284, d162362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16284, d162362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro52384 (p : Pattern) (ha : d16290 p = 1) (hb : d162092 p = 1) : d162368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16285 q = 1) (hb : d162092 q = 1) : d162363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16285, d162363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52383 q ha hb
    | true =>
      simp only [d16285, d162363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16286 q = 1) (hb : d162092 q = 1) : d162364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16286, d162364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16286, d162364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16234 q = 1) (hb : d162092 q = 1) : d162316 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52371 q ha hb
    | true =>
      simp only [d16234, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16235 q = 1) (hb : d162092 q = 1) : d162317 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16287 q = 1) (hb : d162092 q = 1) : d162365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16287, d162365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16287, d162365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16288 q = 1) (hb : d162092 q = 1) : d162366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16288, d162366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16288, d162366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16289 q = 1) (hb : d162092 q = 1) : d162367 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16289, d162367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16289, d162367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16290 q = 1) (hb : d162092 q = 1) : d162368 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16290, d162368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16290, d162368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52385 (p : Pattern) (ha : d16314 p = 1) (hb : d162092 p = 1) : d162374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d162092 q = 1) : d162316 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52371 q ha hb
    | true =>
      simp only [d16234, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d162092 q = 1) : d162317 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16311 q = 1) (hb : d162092 q = 1) : d162371 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16311, d162371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16311, d162371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16312 q = 1) (hb : d162092 q = 1) : d162372 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16312, d162372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16312, d162372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16313 q = 1) (hb : d162092 q = 1) : d162373 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16313, d162373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16313, d162373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16314 q = 1) (hb : d162092 q = 1) : d162374 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16314, d162374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16314, d162374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52386 (p : Pattern) (ha : d128274 p = 1) (hb : d162092 p = 1) : d162380 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16260 q = 1) (hb : d162092 q = 1) : d162342 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16260, d162342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52379 q ha hb
    | true =>
      simp only [d16260, d162342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52377 q ha hb
  have h2 (q : Pattern) (ha : d16261 q = 1) (hb : d162092 q = 1) : d162343 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16261, d162343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16261, d162343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16262 q = 1) (hb : d162092 q = 1) : d162344 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16262, d162344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16262, d162344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16263 q = 1) (hb : d162092 q = 1) : d162345 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16263, d162345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16263, d162345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16267 q = 1) (hb : d162092 q = 1) : d162349 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16267, d162349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52380 q ha hb
    | true =>
      simp only [d16267, d162349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52378 q ha hb
  have h6 (q : Pattern) (ha : d16268 q = 1) (hb : d162092 q = 1) : d162350 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16268, d162350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16268, d162350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16269 q = 1) (hb : d162092 q = 1) : d162351 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16269, d162351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16269, d162351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16291 q = 1) (hb : d162092 q = 1) : d162369 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16291, d162369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52384 q ha hb
    | true =>
      simp only [d16291, d162369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52372 q ha hb
  have h9 (q : Pattern) (ha : d128270 q = 1) (hb : d162092 q = 1) : d162370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128270, d162370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128270, d162370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16315 q = 1) (hb : d162092 q = 1) : d162375 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16315, d162375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52385 q ha hb
    | true =>
      simp only [d16315, d162375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16316 q = 1) (hb : d162092 q = 1) : d162376 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16316, d162376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16316, d162376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128271 q = 1) (hb : d162092 q = 1) : d162377 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128271, d162377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128271, d162377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128272 q = 1) (hb : d162092 q = 1) : d162378 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128272, d162378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128272, d162378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128273 q = 1) (hb : d162092 q = 1) : d162379 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128273, d162379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128273, d162379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128274 q = 1) (hb : d162092 q = 1) : d162380 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128274, d162380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128274, d162380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro52387 (p : Pattern) (ha : d916 p = 1) (hb : d162092 p = 1) : d12804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d162092 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52361 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d162092 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d162092 q = 1) : d12704 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d162092 q = 1) : d12705 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d162092 q = 1) : d12729 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d12729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d12729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d916 q = 1) (hb : d162092 q = 1) : d12804 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, d12804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d916, d12804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52388 (p : Pattern) (ha : d922 p = 1) (hb : d162092 p = 1) : d12810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d162092 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52361 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d162092 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d162092 q = 1) : d12704 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d162092 q = 1) : d12738 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d12738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d12738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d162092 q = 1) : d12739 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d12739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d12739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d922 q = 1) (hb : d162092 q = 1) : d12810 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, d12810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d922, d12810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52389 (p : Pattern) (ha : d16321 p = 1) (hb : d162092 p = 1) : d162381 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d162092 q = 1) : d162316 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52371 q ha hb
    | true =>
      simp only [d16234, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d162092 q = 1) : d162317 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d162092 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52361 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d162092 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d162092 q = 1) : d162318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d162092 q = 1) : d162319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16258 q = 1) (hb : d162092 q = 1) : d162340 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16258, d162340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16258, d162340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16321 q = 1) (hb : d162092 q = 1) : d162381 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16321, d162381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16321, d162381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52390 (p : Pattern) (ha : d16326 p = 1) (hb : d162092 p = 1) : d162386 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d162092 q = 1) : d162316 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52371 q ha hb
    | true =>
      simp only [d16234, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d162092 q = 1) : d162317 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d162092 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52361 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d162092 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d162092 q = 1) : d162318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16264 q = 1) (hb : d162092 q = 1) : d162346 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16264, d162346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16264, d162346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16265 q = 1) (hb : d162092 q = 1) : d162347 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16265, d162347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16265, d162347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16326 q = 1) (hb : d162092 q = 1) : d162386 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16326, d162386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16326, d162386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52391 (p : Pattern) (ha : d16330 p = 1) (hb : d162092 p = 1) : d162390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16285 q = 1) (hb : d162092 q = 1) : d162363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16285, d162363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52383 q ha hb
    | true =>
      simp only [d16285, d162363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16286 q = 1) (hb : d162092 q = 1) : d162364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16286, d162364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16286, d162364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16234 q = 1) (hb : d162092 q = 1) : d162316 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52371 q ha hb
    | true =>
      simp only [d16234, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16235 q = 1) (hb : d162092 q = 1) : d162317 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16287 q = 1) (hb : d162092 q = 1) : d162365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16287, d162365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16287, d162365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16288 q = 1) (hb : d162092 q = 1) : d162366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16288, d162366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16288, d162366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16289 q = 1) (hb : d162092 q = 1) : d162367 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16289, d162367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16289, d162367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16330 q = 1) (hb : d162092 q = 1) : d162390 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16330, d162390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16330, d162390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52392 (p : Pattern) (ha : d16335 p = 1) (hb : d162092 p = 1) : d162393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d162092 q = 1) : d162316 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52371 q ha hb
    | true =>
      simp only [d16234, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d162092 q = 1) : d162317 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16311 q = 1) (hb : d162092 q = 1) : d162371 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16311, d162371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16311, d162371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16312 q = 1) (hb : d162092 q = 1) : d162372 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16312, d162372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16312, d162372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16313 q = 1) (hb : d162092 q = 1) : d162373 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16313, d162373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16313, d162373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16335 q = 1) (hb : d162092 q = 1) : d162393 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16335, d162393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16335, d162393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52393 (p : Pattern) (ha : d128279 p = 1) (hb : d162092 p = 1) : d162399 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16260 q = 1) (hb : d162092 q = 1) : d162342 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16260, d162342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52379 q ha hb
    | true =>
      simp only [d16260, d162342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52377 q ha hb
  have h2 (q : Pattern) (ha : d16261 q = 1) (hb : d162092 q = 1) : d162343 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16261, d162343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16261, d162343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16262 q = 1) (hb : d162092 q = 1) : d162344 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16262, d162344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16262, d162344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16263 q = 1) (hb : d162092 q = 1) : d162345 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16263, d162345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16263, d162345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16267 q = 1) (hb : d162092 q = 1) : d162349 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16267, d162349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52380 q ha hb
    | true =>
      simp only [d16267, d162349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52378 q ha hb
  have h6 (q : Pattern) (ha : d16268 q = 1) (hb : d162092 q = 1) : d162350 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16268, d162350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16268, d162350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16269 q = 1) (hb : d162092 q = 1) : d162351 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16269, d162351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16269, d162351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16291 q = 1) (hb : d162092 q = 1) : d162369 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16291, d162369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52384 q ha hb
    | true =>
      simp only [d16291, d162369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52372 q ha hb
  have h9 (q : Pattern) (ha : d128270 q = 1) (hb : d162092 q = 1) : d162370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128270, d162370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128270, d162370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16315 q = 1) (hb : d162092 q = 1) : d162375 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16315, d162375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52385 q ha hb
    | true =>
      simp only [d16315, d162375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16316 q = 1) (hb : d162092 q = 1) : d162376 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16316, d162376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16316, d162376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128271 q = 1) (hb : d162092 q = 1) : d162377 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128271, d162377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128271, d162377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128272 q = 1) (hb : d162092 q = 1) : d162378 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128272, d162378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128272, d162378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128273 q = 1) (hb : d162092 q = 1) : d162379 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128273, d162379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128273, d162379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16322 q = 1) (hb : d162092 q = 1) : d162382 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16322, d162382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52389 q ha hb
    | true =>
      simp only [d16322, d162382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52387 q ha hb
  have h16 (q : Pattern) (ha : d16323 q = 1) (hb : d162092 q = 1) : d162383 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16323, d162383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16323, d162383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16324 q = 1) (hb : d162092 q = 1) : d162384 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16324, d162384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16324, d162384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16325 q = 1) (hb : d162092 q = 1) : d162385 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16325, d162385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16325, d162385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16327 q = 1) (hb : d162092 q = 1) : d162387 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16327, d162387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52390 q ha hb
    | true =>
      simp only [d16327, d162387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52388 q ha hb
  have h20 (q : Pattern) (ha : d16328 q = 1) (hb : d162092 q = 1) : d162388 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16328, d162388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16328, d162388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16329 q = 1) (hb : d162092 q = 1) : d162389 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16329, d162389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16329, d162389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16331 q = 1) (hb : d162092 q = 1) : d162391 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16331, d162391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52391 q ha hb
    | true =>
      simp only [d16331, d162391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52374 q ha hb
  have h23 (q : Pattern) (ha : d128275 q = 1) (hb : d162092 q = 1) : d162392 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128275, d162392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128275, d162392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16336 q = 1) (hb : d162092 q = 1) : d162394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16336, d162394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52392 q ha hb
    | true =>
      simp only [d16336, d162394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16337 q = 1) (hb : d162092 q = 1) : d162395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16337, d162395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16337, d162395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128276 q = 1) (hb : d162092 q = 1) : d162396 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128276, d162396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128276, d162396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128277 q = 1) (hb : d162092 q = 1) : d162397 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128277, d162397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128277, d162397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128278 q = 1) (hb : d162092 q = 1) : d162398 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128278, d162398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128278, d162398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128279 q = 1) (hb : d162092 q = 1) : d162399 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128279, d162399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128279, d162399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro52394 (p : Pattern) (ha : d128286 p = 1) (hb : d162092 p = 1) : d162408 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16331 q = 1) (hb : d162092 q = 1) : d162391 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16331, d162391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52391 q ha hb
    | true =>
      simp only [d16331, d162391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52374 q ha hb
  have h2 (q : Pattern) (ha : d128275 q = 1) (hb : d162092 q = 1) : d162392 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128275, d162392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128275, d162392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16336 q = 1) (hb : d162092 q = 1) : d162394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16336, d162394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52392 q ha hb
    | true =>
      simp only [d16336, d162394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16337 q = 1) (hb : d162092 q = 1) : d162395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16337, d162395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16337, d162395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128276 q = 1) (hb : d162092 q = 1) : d162396 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128276, d162396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128276, d162396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128284 q = 1) (hb : d162092 q = 1) : d162406 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128284, d162406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128284, d162406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128285 q = 1) (hb : d162092 q = 1) : d162407 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128285, d162407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128285, d162407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128286 q = 1) (hb : d162092 q = 1) : d162408 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128286, d162408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128286, d162408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52395 (p : Pattern) (ha : d16362 p = 1) (hb : d162092 p = 1) : d162415 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d968 q = 1) : d968 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16356 q = 1) (hb : d116750 q = 1) : d21309 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16356, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16356, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51657 q ha hb
  have h3 (q : Pattern) (ha : d9587 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51657 q ha hb
    | true =>
      simp only [d9587, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16357 q = 1) (hb : d116750 q = 1) : d21310 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16357, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16357, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9589 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9589, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9589, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d16358 q = 1) (hb : d116750 q = 1) : d21311 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16358, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16358, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16359 q = 1) (hb : d116750 q = 1) : d21312 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16359, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16359, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d16360 q = 1) (hb : d162091 q = 1) : d162414 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16360, d162091, d162414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16360, d162091, d162414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16361 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16362 q = 1) (hb : d162092 q = 1) : d162415 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16362, d162092, d162415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16362, d162092, d162415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro52396 (p : Pattern) (ha : d16363 p = 1) (hb : d162092 p = 1) : d162264 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d662 q = 1) : d662 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16156 q = 1) (hb : d116750 q = 1) : d21071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16156, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51611 q ha hb
  have h3 (q : Pattern) (ha : d9458 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51611 q ha hb
    | true =>
      simp only [d9458, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16157 q = 1) (hb : d116750 q = 1) : d21072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16157, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9460 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9460, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d16158 q = 1) (hb : d116750 q = 1) : d21073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16158, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16158, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16159 q = 1) (hb : d116750 q = 1) : d21074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16159, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16159, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d16160 q = 1) (hb : d162091 q = 1) : d162263 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16160, d162091, d162263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16160, d162091, d162263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d12862 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16363 q = 1) (hb : d162092 q = 1) : d162264 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16363, d162092, d162264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16363, d162092, d162264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro52397 (p : Pattern) (ha : d16367 p = 1) (hb : d162092 p = 1) : d12863 p = 1 := by
  have h0 (q : Pattern) (ha : d12862 q = 1) (hb : d162091 q = 1) : d12862 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16367 q = 1) (hb : d162092 q = 1) : d12863 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16367, d162092, d12863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16367, d162092, d12863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52398 (p : Pattern) (ha : d16377 p = 1) (hb : d162092 p = 1) : d162425 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16364 q = 1) (hb : d162092 q = 1) : d162416 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16364, d162416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52395 q ha hb
    | true =>
      simp only [d16364, d162416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52396 q ha hb
  have h2 (q : Pattern) (ha : d16365 q = 1) (hb : d162092 q = 1) : d162417 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16365, d162417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16365, d162417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16366 q = 1) (hb : d162092 q = 1) : d162418 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16366, d162418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16366, d162418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16368 q = 1) (hb : d162092 q = 1) : d162419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16368, d162419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52396 q ha hb
    | true =>
      simp only [d16368, d162419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52397 q ha hb
  have h5 (q : Pattern) (ha : d16369 q = 1) (hb : d162092 q = 1) : d162420 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16369, d162420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16369, d162420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16370 q = 1) (hb : d162092 q = 1) : d162421 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16370, d162421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16370, d162421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16371 q = 1) (hb : d162092 q = 1) : d162422 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16371, d162422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16371, d162422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16372 q = 1) (hb : d162092 q = 1) : d162265 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d162265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52396 q ha hb
    | true =>
      simp only [d16372, d162265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52366 q ha hb
  have h9 (q : Pattern) (ha : d16373 q = 1) (hb : d162092 q = 1) : d162266 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d162266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16373, d162266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16374 q = 1) (hb : d162092 q = 1) : d162267 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d162267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, d162267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d986 q = 1) (hb : d162092 q = 1) : d986 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d987 q = 1) (hb : d162092 q = 1) : d6211 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d6211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52366 q ha hb
    | true =>
      simp only [d987, d6211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d988 q = 1) (hb : d162092 q = 1) : d6212 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d6212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d6212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d989 q = 1) (hb : d162092 q = 1) : d6213 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d6213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d6213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16375 q = 1) (hb : d162092 q = 1) : d162423 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d162423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16375, d162423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16376 q = 1) (hb : d162092 q = 1) : d162424 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16376, d162424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16376, d162424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16377 q = 1) (hb : d162092 q = 1) : d162425 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16377, d162425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16377, d162425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro52399 (p : Pattern) (ha : d16381 p = 1) (hb : d162092 p = 1) : d162429 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16372 q = 1) (hb : d162092 q = 1) : d162265 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d162265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52396 q ha hb
    | true =>
      simp only [d16372, d162265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52366 q ha hb
  have h2 (q : Pattern) (ha : d16373 q = 1) (hb : d162092 q = 1) : d162266 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d162266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16373, d162266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16374 q = 1) (hb : d162092 q = 1) : d162267 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d162267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, d162267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d986 q = 1) (hb : d162092 q = 1) : d986 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d987 q = 1) (hb : d162092 q = 1) : d6211 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d6211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52366 q ha hb
    | true =>
      simp only [d987, d6211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d988 q = 1) (hb : d162092 q = 1) : d6212 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d6212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d6212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d989 q = 1) (hb : d162092 q = 1) : d6213 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d6213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d6213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16375 q = 1) (hb : d162092 q = 1) : d162423 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d162423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16375, d162423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d995 q = 1) (hb : d162092 q = 1) : d6214 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d6214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d995, d6214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16380 q = 1) (hb : d162092 q = 1) : d162428 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16380, d162428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16380, d162428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16381 q = 1) (hb : d162092 q = 1) : d162429 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16381, d162429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16381, d162429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro52400 (p : Pattern) (ha : d16387 p = 1) (hb : d162092 p = 1) : d162435 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16378 q = 1) (hb : d162092 q = 1) : d162426 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16378, d162426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52398 q ha hb
    | true =>
      simp only [d16378, d162426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16379 q = 1) (hb : d162092 q = 1) : d162427 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16379, d162427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16379, d162427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16382 q = 1) (hb : d162092 q = 1) : d162430 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d162430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52399 q ha hb
    | true =>
      simp only [d16382, d162430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16383 q = 1) (hb : d162092 q = 1) : d162431 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d162431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d162431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16384 q = 1) (hb : d162092 q = 1) : d162432 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16384, d162432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16384, d162432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16385 q = 1) (hb : d162092 q = 1) : d162433 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16385, d162433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16385, d162433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16386 q = 1) (hb : d162092 q = 1) : d162434 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16386, d162434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16386, d162434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16387 q = 1) (hb : d162092 q = 1) : d162435 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16387, d162435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16387, d162435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52401 (p : Pattern) (ha : d16391 p = 1) (hb : d162092 p = 1) : d162439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16382 q = 1) (hb : d162092 q = 1) : d162430 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d162430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52399 q ha hb
    | true =>
      simp only [d16382, d162430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16383 q = 1) (hb : d162092 q = 1) : d162431 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d162431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d162431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d162092 q = 1) : d12886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d12886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52367 q ha hb
    | true =>
      simp only [d1006, d12886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d162092 q = 1) : d12887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d12887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d12887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16388 q = 1) (hb : d162092 q = 1) : d162436 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16388, d162436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16388, d162436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16389 q = 1) (hb : d162092 q = 1) : d162437 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16389, d162437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16389, d162437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16390 q = 1) (hb : d162092 q = 1) : d162438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16390, d162438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16390, d162438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16391 q = 1) (hb : d162092 q = 1) : d162439 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16391, d162439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16391, d162439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52402 (p : Pattern) (ha : d16417 p = 1) (hb : d162092 p = 1) : d162445 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16382 q = 1) (hb : d162092 q = 1) : d162430 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d162430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52399 q ha hb
    | true =>
      simp only [d16382, d162430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16383 q = 1) (hb : d162092 q = 1) : d162431 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d162431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d162431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16414 q = 1) (hb : d162092 q = 1) : d162442 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16414, d162442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16414, d162442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16415 q = 1) (hb : d162092 q = 1) : d162443 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16415, d162443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16415, d162443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16416 q = 1) (hb : d162092 q = 1) : d162444 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16416, d162444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16416, d162444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16417 q = 1) (hb : d162092 q = 1) : d162445 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16417, d162445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16417, d162445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52403 (p : Pattern) (ha : d128296 p = 1) (hb : d162092 p = 1) : d162451 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16392 q = 1) (hb : d162092 q = 1) : d162440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16392, d162440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52400 q ha hb
    | true =>
      simp only [d16392, d162440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52401 q ha hb
  have h2 (q : Pattern) (ha : d128292 q = 1) (hb : d162092 q = 1) : d162441 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128292, d162441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128292, d162441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16418 q = 1) (hb : d162092 q = 1) : d162446 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16418, d162446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52402 q ha hb
    | true =>
      simp only [d16418, d162446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16419 q = 1) (hb : d162092 q = 1) : d162447 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16419, d162447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16419, d162447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128293 q = 1) (hb : d162092 q = 1) : d162448 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128293, d162448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128293, d162448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128294 q = 1) (hb : d162092 q = 1) : d162449 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128294, d162449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128294, d162449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128295 q = 1) (hb : d162092 q = 1) : d162450 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128295, d162450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128295, d162450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128296 q = 1) (hb : d162092 q = 1) : d162451 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128296, d162451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128296, d162451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52404 (p : Pattern) (ha : d128302 p = 1) (hb : d162092 p = 1) : d162457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16246 q = 1) (hb : d162092 q = 1) : d162328 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16246, d162328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16246, d162328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52373 q ha hb
  have h2 (q : Pattern) (ha : d16247 q = 1) (hb : d162092 q = 1) : d162329 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16247, d162329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16247, d162329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16255 q = 1) (hb : d162092 q = 1) : d162337 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16255, d162337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52373 q ha hb
    | true =>
      simp only [d16255, d162337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52375 q ha hb
  have h4 (q : Pattern) (ha : d16256 q = 1) (hb : d162092 q = 1) : d162338 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16256, d162338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16256, d162338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16257 q = 1) (hb : d162092 q = 1) : d162339 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16257, d162339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16257, d162339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128280 q = 1) (hb : d162092 q = 1) : d162400 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128280, d162400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52386 q ha hb
    | true =>
      simp only [d128280, d162400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52393 q ha hb
  have h7 (q : Pattern) (ha : d16344 q = 1) (hb : d162092 q = 1) : d162402 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16344, d162402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52376 q ha hb
    | true =>
      simp only [d16344, d162402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52364 q ha hb
  have h8 (q : Pattern) (ha : d128281 q = 1) (hb : d162092 q = 1) : d162403 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128281, d162403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128281, d162403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128282 q = 1) (hb : d162092 q = 1) : d162404 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128282, d162404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128282, d162404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128283 q = 1) (hb : d162092 q = 1) : d162405 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128283, d162405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128283, d162405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128287 q = 1) (hb : d162092 q = 1) : d162409 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128287, d162409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128287, d162409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52394 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d162092 q = 1) : d12849 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d12849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d12849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52365 q ha hb
  have h13 (q : Pattern) (ha : d128288 q = 1) (hb : d162092 q = 1) : d162410 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128288, d162410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128288, d162410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128289 q = 1) (hb : d162092 q = 1) : d162411 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128289, d162411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128289, d162411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128290 q = 1) (hb : d162092 q = 1) : d162412 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128290, d162412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128290, d162412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128291 q = 1) (hb : d162092 q = 1) : d162413 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128291, d162413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128291, d162413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128297 q = 1) (hb : d162092 q = 1) : d162452 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128297, d162452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128297, d162452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52403 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d162092 q = 1) : d12942 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d12942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d12942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52369 q ha hb
  have h19 (q : Pattern) (ha : d128298 q = 1) (hb : d162092 q = 1) : d162453 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128298, d162453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128298, d162453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128299 q = 1) (hb : d162092 q = 1) : d162454 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128299, d162454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128299, d162454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128300 q = 1) (hb : d162092 q = 1) : d162455 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128300, d162455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128300, d162455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128301 q = 1) (hb : d162092 q = 1) : d162456 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128301, d162456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128301, d162456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128302 q = 1) (hb : d162092 q = 1) : d162457 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128302, d162457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128302, d162457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro52405 (p : Pattern) (ha : d128308 p = 1) (hb : d162092 p = 1) : d162463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128303 q = 1) (hb : d162092 q = 1) : d162458 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128303, d162458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128303, d162458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52404 q ha hb
  have h2 (q : Pattern) (ha : d128304 q = 1) (hb : d162092 q = 1) : d162459 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128304, d162459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128304, d162459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128305 q = 1) (hb : d162092 q = 1) : d162460 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128305, d162460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128305, d162460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128306 q = 1) (hb : d162092 q = 1) : d162461 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128306, d162461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128306, d162461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128307 q = 1) (hb : d162092 q = 1) : d162462 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128307, d162462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128307, d162462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128308 q = 1) (hb : d162092 q = 1) : d162463 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128308, d162463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128308, d162463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52406 (p : Pattern) (ha : d14773 p = 1) (hb : d162092 p = 1) : d5023 p = 1 := by
  have h0 (q : Pattern) (ha : d5022 q = 1) (hb : d162091 q = 1) : d5022 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14772 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14773 q = 1) (hb : d162092 q = 1) : d5023 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14773, d162092, d5023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14773, d162092, d5023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52407 (p : Pattern) (ha : d14778 p = 1) (hb : d162092 p = 1) : d12961 p = 1 := by
  have h0 (q : Pattern) (ha : d1127 q = 1) (hb : d162091 q = 1) : d1127 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14772 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14778 q = 1) (hb : d162092 q = 1) : d12961 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14778, d162092, d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14778, d162092, d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52408 (p : Pattern) (ha : d16442 p = 1) (hb : d162092 p = 1) : d162467 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1103 q = 1) : d1103 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9789 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51685 q ha hb
    | true =>
      simp only [d9789, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9791 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9791, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9791, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16438 q = 1) (hb : d116750 q = 1) : d21744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16438, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16438, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16439 q = 1) (hb : d116750 q = 1) : d21745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16439, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16439, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d16440 q = 1) (hb : d162091 q = 1) : d162466 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16440, d162091, d162466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16440, d162091, d162466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d16441 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d16442 q = 1) (hb : d162092 q = 1) : d162467 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16442, d162092, d162467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16442, d162092, d162467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro52409 (p : Pattern) (ha : d16443 p = 1) (hb : d162092 p = 1) : d162469 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1113 q = 1) : d1113 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1123 q = 1) (hb : d116750 q = 1) : d21757 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1124 q = 1) (hb : d116750 q = 1) : d21758 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1125 q = 1) (hb : d162091 q = 1) : d162468 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d162091, d162468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1125, d162091, d162468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d14765 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d16443 q = 1) (hb : d162092 q = 1) : d162469 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16443, d162092, d162469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16443, d162092, d162469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro52410 (p : Pattern) (ha : d16456 p = 1) (hb : d162092 p = 1) : d162482 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d162092 q = 1) : d162470 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d162470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52408 q ha hb
    | true =>
      simp only [d16444, d162470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52409 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d162092 q = 1) : d162471 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d162471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d162471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d162092 q = 1) : d162472 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d162472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d162472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16447 q = 1) (hb : d162092 q = 1) : d162473 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d162473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52409 q ha hb
    | true =>
      simp only [d16447, d162473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52406 q ha hb
  have h5 (q : Pattern) (ha : d16448 q = 1) (hb : d162092 q = 1) : d162474 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d162474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d162474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16449 q = 1) (hb : d162092 q = 1) : d162475 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d162475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d162475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16450 q = 1) (hb : d162092 q = 1) : d162476 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d162476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d162476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16451 q = 1) (hb : d162092 q = 1) : d162477 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, d162477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52409 q ha hb
    | true =>
      simp only [d16451, d162477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52407 q ha hb
  have h9 (q : Pattern) (ha : d16452 q = 1) (hb : d162092 q = 1) : d162478 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16452, d162478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16452, d162478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16453 q = 1) (hb : d162092 q = 1) : d162479 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16453, d162479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16453, d162479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16454 q = 1) (hb : d162092 q = 1) : d162480 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16454, d162480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16454, d162480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16455 q = 1) (hb : d162092 q = 1) : d162481 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16455, d162481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16455, d162481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16456 q = 1) (hb : d162092 q = 1) : d162482 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16456, d162482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16456, d162482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro52411 (p : Pattern) (ha : d16460 p = 1) (hb : d162092 p = 1) : d162486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16451 q = 1) (hb : d162092 q = 1) : d162477 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, d162477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52409 q ha hb
    | true =>
      simp only [d16451, d162477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52407 q ha hb
  have h2 (q : Pattern) (ha : d16452 q = 1) (hb : d162092 q = 1) : d162478 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16452, d162478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16452, d162478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16453 q = 1) (hb : d162092 q = 1) : d162479 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16453, d162479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16453, d162479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16454 q = 1) (hb : d162092 q = 1) : d162480 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16454, d162480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16454, d162480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16459 q = 1) (hb : d162092 q = 1) : d162485 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16459, d162485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16459, d162485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16460 q = 1) (hb : d162092 q = 1) : d162486 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16460, d162486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16460, d162486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52412 (p : Pattern) (ha : d16466 p = 1) (hb : d162092 p = 1) : d162492 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d162092 q = 1) : d162483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52410 q ha hb
    | true =>
      simp only [d16457, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d162092 q = 1) : d162484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52411 q ha hb
    | true =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d162092 q = 1) : d162489 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d162092 q = 1) : d162490 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16465 q = 1) (hb : d162092 q = 1) : d162491 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16465, d162491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16465, d162491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16466 q = 1) (hb : d162092 q = 1) : d162492 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16466, d162492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16466, d162492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52413 (p : Pattern) (ha : d16470 p = 1) (hb : d162092 p = 1) : d162496 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52411 q ha hb
    | true =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d162092 q = 1) : d162493 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d162092 q = 1) : d162494 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16469 q = 1) (hb : d162092 q = 1) : d162495 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16469, d162495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16469, d162495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16470 q = 1) (hb : d162092 q = 1) : d162496 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16470, d162496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16470, d162496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52414 (p : Pattern) (ha : d16476 p = 1) (hb : d162092 p = 1) : d162502 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16471 q = 1) (hb : d162092 q = 1) : d162497 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16471, d162497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52412 q ha hb
    | true =>
      simp only [d16471, d162497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52413 q ha hb
  have h2 (q : Pattern) (ha : d16472 q = 1) (hb : d162092 q = 1) : d162498 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16472, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16472, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16473 q = 1) (hb : d162092 q = 1) : d162499 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16473, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16473, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16474 q = 1) (hb : d162092 q = 1) : d162500 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16474, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16474, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16475 q = 1) (hb : d162092 q = 1) : d162501 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16475, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16475, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16476 q = 1) (hb : d162092 q = 1) : d162502 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16476, d162502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16476, d162502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52415 (p : Pattern) (ha : d16479 p = 1) (hb : d162092 p = 1) : d162505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d162092 q = 1) : d162483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52410 q ha hb
    | true =>
      simp only [d16457, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d162092 q = 1) : d162484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52411 q ha hb
    | true =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d162092 q = 1) : d162489 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d162092 q = 1) : d162490 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16465 q = 1) (hb : d162092 q = 1) : d162491 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16465, d162491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16465, d162491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16479 q = 1) (hb : d162092 q = 1) : d162505 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16479, d162505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16479, d162505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52416 (p : Pattern) (ha : d16480 p = 1) (hb : d162092 p = 1) : d162506 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52411 q ha hb
    | true =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d162092 q = 1) : d162493 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d162092 q = 1) : d162494 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16469 q = 1) (hb : d162092 q = 1) : d162495 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16469, d162495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16469, d162495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16480 q = 1) (hb : d162092 q = 1) : d162506 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16480, d162506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16480, d162506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52417 (p : Pattern) (ha : d16486 p = 1) (hb : d162092 p = 1) : d162512 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16471 q = 1) (hb : d162092 q = 1) : d162497 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16471, d162497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52412 q ha hb
    | true =>
      simp only [d16471, d162497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52413 q ha hb
  have h2 (q : Pattern) (ha : d16472 q = 1) (hb : d162092 q = 1) : d162498 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16472, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16472, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16473 q = 1) (hb : d162092 q = 1) : d162499 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16473, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16473, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16474 q = 1) (hb : d162092 q = 1) : d162500 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16474, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16474, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16475 q = 1) (hb : d162092 q = 1) : d162501 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16475, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16475, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16481 q = 1) (hb : d162092 q = 1) : d162507 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16481, d162507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52415 q ha hb
    | true =>
      simp only [d16481, d162507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52416 q ha hb
  have h7 (q : Pattern) (ha : d16482 q = 1) (hb : d162092 q = 1) : d162508 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16482, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16482, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16483 q = 1) (hb : d162092 q = 1) : d162509 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16483, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16483, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16484 q = 1) (hb : d162092 q = 1) : d162510 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16484, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16484, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16485 q = 1) (hb : d162092 q = 1) : d162511 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16485, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16485, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16486 q = 1) (hb : d162092 q = 1) : d162512 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16486, d162512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16486, d162512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52418 (p : Pattern) (ha : d16527 p = 1) (hb : d162092 p = 1) : d162548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d162092 q = 1) : d162470 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d162470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52408 q ha hb
    | true =>
      simp only [d16444, d162470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52409 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d162092 q = 1) : d162471 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d162471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d162471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d162092 q = 1) : d162472 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d162472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d162472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16447 q = 1) (hb : d162092 q = 1) : d162473 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d162473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52409 q ha hb
    | true =>
      simp only [d16447, d162473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52406 q ha hb
  have h5 (q : Pattern) (ha : d16448 q = 1) (hb : d162092 q = 1) : d162474 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d162474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d162474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16449 q = 1) (hb : d162092 q = 1) : d162475 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d162475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d162475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16450 q = 1) (hb : d162092 q = 1) : d162476 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d162476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d162476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16525 q = 1) (hb : d162092 q = 1) : d162546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16525, d162546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16525, d162546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16526 q = 1) (hb : d162092 q = 1) : d162547 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16526, d162547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16526, d162547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16527 q = 1) (hb : d162092 q = 1) : d162548 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16527, d162548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16527, d162548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro52419 (p : Pattern) (ha : d16537 p = 1) (hb : d162092 p = 1) : d162558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16528 q = 1) (hb : d162092 q = 1) : d162549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52418 q ha hb
    | true =>
      simp only [d16528, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16529 q = 1) (hb : d162092 q = 1) : d162550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52411 q ha hb
    | true =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16534 q = 1) (hb : d162092 q = 1) : d162555 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16534, d162555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16534, d162555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16535 q = 1) (hb : d162092 q = 1) : d162556 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16535, d162556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16535, d162556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16536 q = 1) (hb : d162092 q = 1) : d162557 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16536, d162557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16536, d162557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16537 q = 1) (hb : d162092 q = 1) : d162558 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16537, d162558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16537, d162558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52420 (p : Pattern) (ha : d16628 p = 1) (hb : d162092 p = 1) : d162604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16618 q = 1) (hb : d162092 q = 1) : d162594 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16618, d162594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52419 q ha hb
    | true =>
      simp only [d16618, d162594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52413 q ha hb
  have h2 (q : Pattern) (ha : d16619 q = 1) (hb : d162092 q = 1) : d162595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16619, d162595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16619, d162595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16620 q = 1) (hb : d162092 q = 1) : d162596 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16620, d162596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16620, d162596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16621 q = 1) (hb : d162092 q = 1) : d162597 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16621, d162597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16621, d162597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16622 q = 1) (hb : d162092 q = 1) : d162598 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16622, d162598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16622, d162598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16623 q = 1) (hb : d162092 q = 1) : d162599 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16623, d162599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52413 q ha hb
    | true =>
      simp only [d16623, d162599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16624 q = 1) (hb : d162092 q = 1) : d162600 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16624, d162600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16624, d162600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16625 q = 1) (hb : d162092 q = 1) : d162601 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16625, d162601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16625, d162601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16626 q = 1) (hb : d162092 q = 1) : d162602 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16626, d162602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16626, d162602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16627 q = 1) (hb : d162092 q = 1) : d162603 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16627, d162603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16627, d162603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16628 q = 1) (hb : d162092 q = 1) : d162604 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16628, d162604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16628, d162604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52421 (p : Pattern) (ha : d16634 p = 1) (hb : d162092 p = 1) : d162610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16623 q = 1) (hb : d162092 q = 1) : d162599 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16623, d162599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52413 q ha hb
    | true =>
      simp only [d16623, d162599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16624 q = 1) (hb : d162092 q = 1) : d162600 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16624, d162600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16624, d162600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16625 q = 1) (hb : d162092 q = 1) : d162601 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16625, d162601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16625, d162601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16626 q = 1) (hb : d162092 q = 1) : d162602 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16626, d162602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16626, d162602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16627 q = 1) (hb : d162092 q = 1) : d162603 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16627, d162603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16627, d162603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16629 q = 1) (hb : d162092 q = 1) : d162605 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16629, d162605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52416 q ha hb
    | true =>
      simp only [d16629, d162605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16630 q = 1) (hb : d162092 q = 1) : d162606 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16630, d162606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16630, d162606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16631 q = 1) (hb : d162092 q = 1) : d162607 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16631, d162607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16631, d162607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16632 q = 1) (hb : d162092 q = 1) : d162608 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16632, d162608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16632, d162608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16633 q = 1) (hb : d162092 q = 1) : d162609 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16633, d162609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16633, d162609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16634 q = 1) (hb : d162092 q = 1) : d162610 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16634, d162610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16634, d162610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52422 (p : Pattern) (ha : d16643 p = 1) (hb : d162092 p = 1) : d162619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16629 q = 1) (hb : d162092 q = 1) : d162605 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16629, d162605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52416 q ha hb
    | true =>
      simp only [d16629, d162605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16630 q = 1) (hb : d162092 q = 1) : d162606 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16630, d162606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16630, d162606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16631 q = 1) (hb : d162092 q = 1) : d162607 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16631, d162607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16631, d162607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16632 q = 1) (hb : d162092 q = 1) : d162608 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16632, d162608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16632, d162608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16633 q = 1) (hb : d162092 q = 1) : d162609 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16633, d162609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16633, d162609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16643 q = 1) (hb : d162092 q = 1) : d162619 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16643, d162619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16643, d162619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52423 (p : Pattern) (ha : d15042 p = 1) (hb : d162092 p = 1) : d13190 p = 1 := by
  have h0 (q : Pattern) (ha : d1400 q = 1) (hb : d162091 q = 1) : d1400 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15023 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15042 q = 1) (hb : d162092 q = 1) : d13190 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15042, d162092, d13190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15042, d162092, d13190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52424 (p : Pattern) (ha : d16672 p = 1) (hb : d162092 p = 1) : d162637 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1388 q = 1) : d1388 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1391 q = 1) (hb : d116750 q = 1) : d22064 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
  have h3 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1392 q = 1) (hb : d116750 q = 1) : d22065 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1393 q = 1) (hb : d116750 q = 1) : d22066 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1394 q = 1) (hb : d116750 q = 1) : d22067 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1395 q = 1) (hb : d162091 q = 1) : d162636 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d162091, d162636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1395, d162091, d162636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d15008 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16672 q = 1) (hb : d162092 q = 1) : d162637 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16672, d162092, d162637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16672, d162092, d162637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro52425 (p : Pattern) (ha : d16698 p = 1) (hb : d162092 p = 1) : d162663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16693 q = 1) (hb : d162092 q = 1) : d162658 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d162658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52424 q ha hb
    | true =>
      simp only [d16693, d162658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52423 q ha hb
  have h2 (q : Pattern) (ha : d16694 q = 1) (hb : d162092 q = 1) : d162659 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d162659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d162659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16695 q = 1) (hb : d162092 q = 1) : d162660 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d162660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d162660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16696 q = 1) (hb : d162092 q = 1) : d162661 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d162661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16696, d162661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16697 q = 1) (hb : d162092 q = 1) : d162662 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16697, d162662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16697, d162662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16698 q = 1) (hb : d162092 q = 1) : d162663 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16698, d162663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16698, d162663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52426 (p : Pattern) (ha : d16765 p = 1) (hb : d162092 p = 1) : d162690 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16699 q = 1) (hb : d162092 q = 1) : d162664 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d162664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52425 q ha hb
    | true =>
      simp only [d16699, d162664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16700 q = 1) (hb : d162092 q = 1) : d162665 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d162665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d162665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16762 q = 1) (hb : d162092 q = 1) : d162687 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16762, d162687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16762, d162687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16763 q = 1) (hb : d162092 q = 1) : d162688 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16763, d162688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16763, d162688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16764 q = 1) (hb : d162092 q = 1) : d162689 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16764, d162689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16764, d162689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16765 q = 1) (hb : d162092 q = 1) : d162690 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16765, d162690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16765, d162690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52427 (p : Pattern) (ha : d16771 p = 1) (hb : d162092 p = 1) : d162696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16766 q = 1) (hb : d162092 q = 1) : d162691 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16766, d162691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52426 q ha hb
    | true =>
      simp only [d16766, d162691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16767 q = 1) (hb : d162092 q = 1) : d162692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16767, d162692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16767, d162692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16768 q = 1) (hb : d162092 q = 1) : d162693 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16768, d162693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16768, d162693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16769 q = 1) (hb : d162092 q = 1) : d162694 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16769, d162694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16769, d162694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16770 q = 1) (hb : d162092 q = 1) : d162695 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16770, d162695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16770, d162695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16771 q = 1) (hb : d162092 q = 1) : d162696 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16771, d162696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16771, d162696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52428 (p : Pattern) (ha : d16491 p = 1) (hb : d162092 p = 1) : d162517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d162092 q = 1) : d162483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52410 q ha hb
    | true =>
      simp only [d16457, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d162092 q = 1) : d162484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52411 q ha hb
    | true =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d162092 q = 1) : d162489 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d162092 q = 1) : d162490 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16490 q = 1) (hb : d162092 q = 1) : d162516 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16490, d162516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16490, d162516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16491 q = 1) (hb : d162092 q = 1) : d162517 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16491, d162517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16491, d162517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52429 (p : Pattern) (ha : d16493 p = 1) (hb : d162092 p = 1) : d162519 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52411 q ha hb
    | true =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d162092 q = 1) : d162493 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d162092 q = 1) : d162494 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16492 q = 1) (hb : d162092 q = 1) : d162518 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16492, d162518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16492, d162518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16493 q = 1) (hb : d162092 q = 1) : d162519 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16493, d162519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16493, d162519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52430 (p : Pattern) (ha : d16500 p = 1) (hb : d162092 p = 1) : d162526 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d162092 q = 1) : d162483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52410 q ha hb
    | true =>
      simp only [d16457, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d162092 q = 1) : d162484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52411 q ha hb
    | true =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d162092 q = 1) : d162489 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16498 q = 1) (hb : d162092 q = 1) : d162524 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16498, d162524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16498, d162524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16499 q = 1) (hb : d162092 q = 1) : d162525 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16499, d162525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16499, d162525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16500 q = 1) (hb : d162092 q = 1) : d162526 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16500, d162526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16500, d162526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52431 (p : Pattern) (ha : d16503 p = 1) (hb : d162092 p = 1) : d162529 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52411 q ha hb
    | true =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d162092 q = 1) : d162493 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16501 q = 1) (hb : d162092 q = 1) : d162527 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16501, d162527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16501, d162527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16502 q = 1) (hb : d162092 q = 1) : d162528 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16502, d162528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16502, d162528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16503 q = 1) (hb : d162092 q = 1) : d162529 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16503, d162529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16503, d162529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52432 (p : Pattern) (ha : d16511 p = 1) (hb : d162092 p = 1) : d162534 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1213 q = 1) : d1213 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9753 q = 1) (hb : d116750 q = 1) : d21737 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9753, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51710 q ha hb
    | true =>
      simp only [d9753, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9755 q = 1) (hb : d116750 q = 1) : d21738 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9755, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9755, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16507 q = 1) (hb : d116750 q = 1) : d21739 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16507, d21739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16507, d21739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16508 q = 1) (hb : d116750 q = 1) : d21740 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16508, d21740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16508, d21740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d16509 q = 1) (hb : d162091 q = 1) : d162533 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16509, d162091, d162533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16509, d162091, d162533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d16510 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d16511 q = 1) (hb : d162092 q = 1) : d162534 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16511, d162092, d162534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16511, d162092, d162534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro52433 (p : Pattern) (ha : d16516 p = 1) (hb : d162092 p = 1) : d13030 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d13023 q = 1) : d13023 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9800 q = 1) (hb : d116750 q = 1) : d13025 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d13025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36939 q ha hb
    | true =>
      simp only [d9800, d13025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9802 q = 1) (hb : d116750 q = 1) : d13026 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d13026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9802, d13026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d14763 q = 1) (hb : d116750 q = 1) : d13027 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d13027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14763, d13027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14764 q = 1) (hb : d116750 q = 1) : d13028 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, d13028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14764, d13028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d16515 q = 1) (hb : d162091 q = 1) : d13029 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16515, d162091, d13029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16515, d162091, d13029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d14765 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d16516 q = 1) (hb : d162092 q = 1) : d13030 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16516, d162092, d13030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16516, d162092, d13030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro52434 (p : Pattern) (ha : d16522 p = 1) (hb : d162092 p = 1) : d162543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16512 q = 1) (hb : d162092 q = 1) : d162535 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16512, d162535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52432 q ha hb
    | true =>
      simp only [d16512, d162535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52408 q ha hb
  have h2 (q : Pattern) (ha : d16513 q = 1) (hb : d162092 q = 1) : d162536 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16513, d162536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16513, d162536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16514 q = 1) (hb : d162092 q = 1) : d162537 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16514, d162537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16514, d162537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16517 q = 1) (hb : d162092 q = 1) : d162538 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16517, d162538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52408 q ha hb
    | true =>
      simp only [d16517, d162538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52433 q ha hb
  have h5 (q : Pattern) (ha : d16518 q = 1) (hb : d162092 q = 1) : d162539 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16518, d162539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16518, d162539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16519 q = 1) (hb : d162092 q = 1) : d162540 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16519, d162540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16519, d162540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16520 q = 1) (hb : d162092 q = 1) : d162541 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16520, d162541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16520, d162541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16444 q = 1) (hb : d162092 q = 1) : d162470 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d162470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52408 q ha hb
    | true =>
      simp only [d16444, d162470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52409 q ha hb
  have h9 (q : Pattern) (ha : d16445 q = 1) (hb : d162092 q = 1) : d162471 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d162471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d162471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16446 q = 1) (hb : d162092 q = 1) : d162472 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d162472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d162472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16447 q = 1) (hb : d162092 q = 1) : d162473 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d162473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52409 q ha hb
    | true =>
      simp only [d16447, d162473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52406 q ha hb
  have h12 (q : Pattern) (ha : d16448 q = 1) (hb : d162092 q = 1) : d162474 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d162474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d162474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16449 q = 1) (hb : d162092 q = 1) : d162475 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d162475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d162475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16450 q = 1) (hb : d162092 q = 1) : d162476 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d162476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16450, d162476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16521 q = 1) (hb : d162092 q = 1) : d162542 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16521, d162542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16521, d162542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16522 q = 1) (hb : d162092 q = 1) : d162543 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16522, d162543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16522, d162543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro52435 (p : Pattern) (ha : d16533 p = 1) (hb : d162092 p = 1) : d162554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16523 q = 1) (hb : d162092 q = 1) : d162544 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16523, d162544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52434 q ha hb
    | true =>
      simp only [d16523, d162544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16524 q = 1) (hb : d162092 q = 1) : d162545 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16524, d162545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16524, d162545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16528 q = 1) (hb : d162092 q = 1) : d162549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52418 q ha hb
    | true =>
      simp only [d16528, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16529 q = 1) (hb : d162092 q = 1) : d162550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16530 q = 1) (hb : d162092 q = 1) : d162551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16530, d162551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16530, d162551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16531 q = 1) (hb : d162092 q = 1) : d162552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16531, d162552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16531, d162552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16532 q = 1) (hb : d162092 q = 1) : d162553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16532, d162553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16532, d162553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16533 q = 1) (hb : d162092 q = 1) : d162554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16533, d162554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16533, d162554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52436 (p : Pattern) (ha : d16579 p = 1) (hb : d162092 p = 1) : d162482 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d162092 q = 1) : d162470 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d162470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52408 q ha hb
    | true =>
      simp only [d16444, d162470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52409 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d162092 q = 1) : d162471 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d162471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d162471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d162092 q = 1) : d162472 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d162472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d162472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16447 q = 1) (hb : d162092 q = 1) : d162473 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d162473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52409 q ha hb
    | true =>
      simp only [d16447, d162473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52406 q ha hb
  have h5 (q : Pattern) (ha : d16448 q = 1) (hb : d162092 q = 1) : d162474 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d162474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d162474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16449 q = 1) (hb : d162092 q = 1) : d162475 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d162475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d162475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16450 q = 1) (hb : d162092 q = 1) : d162476 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d162476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d162476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12961 q = 1) (hb : d162092 q = 1) : d12961 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d16574 q = 1) (hb : d162092 q = 1) : d162477 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16574, d162477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52409 q ha hb
    | true =>
      simp only [d16574, d162477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16575 q = 1) (hb : d162092 q = 1) : d162478 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16575, d162478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16575, d162478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16576 q = 1) (hb : d162092 q = 1) : d162479 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16576, d162479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16576, d162479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16577 q = 1) (hb : d162092 q = 1) : d162480 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16577, d162480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16577, d162480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16578 q = 1) (hb : d162092 q = 1) : d162481 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16578, d162481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16578, d162481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16579 q = 1) (hb : d162092 q = 1) : d162482 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16579, d162482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16579, d162482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro52437 (p : Pattern) (ha : d16585 p = 1) (hb : d162092 p = 1) : d162564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16580 q = 1) (hb : d162092 q = 1) : d162483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16580, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52436 q ha hb
    | true =>
      simp only [d16580, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16581 q = 1) (hb : d162092 q = 1) : d162484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16581, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16581, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16582 q = 1) (hb : d162092 q = 1) : d162561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16582, d162561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16582, d162561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16583 q = 1) (hb : d162092 q = 1) : d162562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16583, d162562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16583, d162562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16584 q = 1) (hb : d162092 q = 1) : d162563 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16584, d162563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16584, d162563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16585 q = 1) (hb : d162092 q = 1) : d162564 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16585, d162564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16585, d162564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52438 (p : Pattern) (ha : d128315 p = 1) (hb : d162092 p = 1) : d162570 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16494 q = 1) (hb : d162092 q = 1) : d162520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16494, d162520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52428 q ha hb
    | true =>
      simp only [d16494, d162520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52429 q ha hb
  have h2 (q : Pattern) (ha : d16495 q = 1) (hb : d162092 q = 1) : d162521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16495, d162521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16495, d162521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16496 q = 1) (hb : d162092 q = 1) : d162522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16496, d162522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16496, d162522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16497 q = 1) (hb : d162092 q = 1) : d162523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16497, d162523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16497, d162523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16504 q = 1) (hb : d162092 q = 1) : d162530 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16504, d162530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52430 q ha hb
    | true =>
      simp only [d16504, d162530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52431 q ha hb
  have h6 (q : Pattern) (ha : d16505 q = 1) (hb : d162092 q = 1) : d162531 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16505, d162531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16505, d162531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16506 q = 1) (hb : d162092 q = 1) : d162532 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16506, d162532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16506, d162532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16538 q = 1) (hb : d162092 q = 1) : d162559 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16538, d162559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52435 q ha hb
    | true =>
      simp only [d16538, d162559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52419 q ha hb
  have h9 (q : Pattern) (ha : d128311 q = 1) (hb : d162092 q = 1) : d162560 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128311, d162560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128311, d162560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16586 q = 1) (hb : d162092 q = 1) : d162565 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16586, d162565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52437 q ha hb
    | true =>
      simp only [d16586, d162565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16587 q = 1) (hb : d162092 q = 1) : d162566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16587, d162566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16587, d162566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128312 q = 1) (hb : d162092 q = 1) : d162567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128312, d162567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128312, d162567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128313 q = 1) (hb : d162092 q = 1) : d162568 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128313, d162568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128313, d162568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128314 q = 1) (hb : d162092 q = 1) : d162569 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128314, d162569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128314, d162569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128315 q = 1) (hb : d162092 q = 1) : d162570 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128315, d162570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128315, d162570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro52439 (p : Pattern) (ha : d16592 p = 1) (hb : d162092 p = 1) : d162571 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d162092 q = 1) : d162483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52410 q ha hb
    | true =>
      simp only [d16457, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d162092 q = 1) : d162484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52411 q ha hb
    | true =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d162092 q = 1) : d162489 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d162092 q = 1) : d162490 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16490 q = 1) (hb : d162092 q = 1) : d162516 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16490, d162516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16490, d162516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16592 q = 1) (hb : d162092 q = 1) : d162571 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16592, d162571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16592, d162571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52440 (p : Pattern) (ha : d16593 p = 1) (hb : d162092 p = 1) : d162572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52411 q ha hb
    | true =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d162092 q = 1) : d162493 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d162092 q = 1) : d162494 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16492 q = 1) (hb : d162092 q = 1) : d162518 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16492, d162518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16492, d162518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16593 q = 1) (hb : d162092 q = 1) : d162572 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16593, d162572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16593, d162572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52441 (p : Pattern) (ha : d16598 p = 1) (hb : d162092 p = 1) : d162577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d162092 q = 1) : d162483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52410 q ha hb
    | true =>
      simp only [d16457, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d162092 q = 1) : d162484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52411 q ha hb
    | true =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d162092 q = 1) : d162489 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16498 q = 1) (hb : d162092 q = 1) : d162524 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16498, d162524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16498, d162524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16499 q = 1) (hb : d162092 q = 1) : d162525 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16499, d162525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16499, d162525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16598 q = 1) (hb : d162092 q = 1) : d162577 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16598, d162577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16598, d162577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52442 (p : Pattern) (ha : d16599 p = 1) (hb : d162092 p = 1) : d162578 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52411 q ha hb
    | true =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d162092 q = 1) : d162493 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16501 q = 1) (hb : d162092 q = 1) : d162527 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16501, d162527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16501, d162527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16502 q = 1) (hb : d162092 q = 1) : d162528 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16502, d162528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16502, d162528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16599 q = 1) (hb : d162092 q = 1) : d162578 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16599, d162578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16599, d162578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52443 (p : Pattern) (ha : d16603 p = 1) (hb : d162092 p = 1) : d162582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16523 q = 1) (hb : d162092 q = 1) : d162544 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16523, d162544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52434 q ha hb
    | true =>
      simp only [d16523, d162544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16524 q = 1) (hb : d162092 q = 1) : d162545 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16524, d162545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16524, d162545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16528 q = 1) (hb : d162092 q = 1) : d162549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52418 q ha hb
    | true =>
      simp only [d16528, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16529 q = 1) (hb : d162092 q = 1) : d162550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16530 q = 1) (hb : d162092 q = 1) : d162551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16530, d162551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16530, d162551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16531 q = 1) (hb : d162092 q = 1) : d162552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16531, d162552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16531, d162552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16532 q = 1) (hb : d162092 q = 1) : d162553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16532, d162553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16532, d162553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16603 q = 1) (hb : d162092 q = 1) : d162582 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16603, d162582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16603, d162582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52444 (p : Pattern) (ha : d16604 p = 1) (hb : d162092 p = 1) : d162583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16528 q = 1) (hb : d162092 q = 1) : d162549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52418 q ha hb
    | true =>
      simp only [d16528, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16529 q = 1) (hb : d162092 q = 1) : d162550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52411 q ha hb
    | true =>
      simp only [d16461, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16534 q = 1) (hb : d162092 q = 1) : d162555 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16534, d162555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16534, d162555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16535 q = 1) (hb : d162092 q = 1) : d162556 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16535, d162556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16535, d162556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16536 q = 1) (hb : d162092 q = 1) : d162557 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16536, d162557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16536, d162557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16604 q = 1) (hb : d162092 q = 1) : d162583 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16604, d162583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16604, d162583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52445 (p : Pattern) (ha : d16610 p = 1) (hb : d162092 p = 1) : d162586 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16580 q = 1) (hb : d162092 q = 1) : d162483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16580, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52436 q ha hb
    | true =>
      simp only [d16580, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16581 q = 1) (hb : d162092 q = 1) : d162484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16581, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16581, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16582 q = 1) (hb : d162092 q = 1) : d162561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16582, d162561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16582, d162561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16583 q = 1) (hb : d162092 q = 1) : d162562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16583, d162562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16583, d162562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16584 q = 1) (hb : d162092 q = 1) : d162563 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16584, d162563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16584, d162563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16610 q = 1) (hb : d162092 q = 1) : d162586 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16610, d162586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16610, d162586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52446 (p : Pattern) (ha : d128320 p = 1) (hb : d162092 p = 1) : d162592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16494 q = 1) (hb : d162092 q = 1) : d162520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16494, d162520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52428 q ha hb
    | true =>
      simp only [d16494, d162520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52429 q ha hb
  have h2 (q : Pattern) (ha : d16495 q = 1) (hb : d162092 q = 1) : d162521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16495, d162521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16495, d162521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16496 q = 1) (hb : d162092 q = 1) : d162522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16496, d162522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16496, d162522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16497 q = 1) (hb : d162092 q = 1) : d162523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16497, d162523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16497, d162523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16504 q = 1) (hb : d162092 q = 1) : d162530 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16504, d162530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52430 q ha hb
    | true =>
      simp only [d16504, d162530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52431 q ha hb
  have h6 (q : Pattern) (ha : d16505 q = 1) (hb : d162092 q = 1) : d162531 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16505, d162531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16505, d162531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16506 q = 1) (hb : d162092 q = 1) : d162532 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16506, d162532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16506, d162532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16538 q = 1) (hb : d162092 q = 1) : d162559 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16538, d162559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52435 q ha hb
    | true =>
      simp only [d16538, d162559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52419 q ha hb
  have h9 (q : Pattern) (ha : d128311 q = 1) (hb : d162092 q = 1) : d162560 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128311, d162560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128311, d162560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16586 q = 1) (hb : d162092 q = 1) : d162565 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16586, d162565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52437 q ha hb
    | true =>
      simp only [d16586, d162565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16587 q = 1) (hb : d162092 q = 1) : d162566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16587, d162566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16587, d162566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128312 q = 1) (hb : d162092 q = 1) : d162567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128312, d162567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128312, d162567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128313 q = 1) (hb : d162092 q = 1) : d162568 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128313, d162568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128313, d162568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128314 q = 1) (hb : d162092 q = 1) : d162569 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128314, d162569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128314, d162569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16594 q = 1) (hb : d162092 q = 1) : d162573 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16594, d162573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52439 q ha hb
    | true =>
      simp only [d16594, d162573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52440 q ha hb
  have h16 (q : Pattern) (ha : d16595 q = 1) (hb : d162092 q = 1) : d162574 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16595, d162574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16595, d162574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16596 q = 1) (hb : d162092 q = 1) : d162575 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16596, d162575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16596, d162575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16597 q = 1) (hb : d162092 q = 1) : d162576 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16597, d162576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16597, d162576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16600 q = 1) (hb : d162092 q = 1) : d162579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16600, d162579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52441 q ha hb
    | true =>
      simp only [d16600, d162579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52442 q ha hb
  have h20 (q : Pattern) (ha : d16601 q = 1) (hb : d162092 q = 1) : d162580 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16601, d162580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16601, d162580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16602 q = 1) (hb : d162092 q = 1) : d162581 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16602, d162581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16602, d162581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16605 q = 1) (hb : d162092 q = 1) : d162584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16605, d162584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52443 q ha hb
    | true =>
      simp only [d16605, d162584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52444 q ha hb
  have h23 (q : Pattern) (ha : d128316 q = 1) (hb : d162092 q = 1) : d162585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128316, d162585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128316, d162585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16611 q = 1) (hb : d162092 q = 1) : d162587 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16611, d162587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52445 q ha hb
    | true =>
      simp only [d16611, d162587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16612 q = 1) (hb : d162092 q = 1) : d162588 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16612, d162588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16612, d162588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128317 q = 1) (hb : d162092 q = 1) : d162589 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128317, d162589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128317, d162589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128318 q = 1) (hb : d162092 q = 1) : d162590 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128318, d162590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128318, d162590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128319 q = 1) (hb : d162092 q = 1) : d162591 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128319, d162591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128319, d162591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128320 q = 1) (hb : d162092 q = 1) : d162592 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128320, d162592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128320, d162592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro52447 (p : Pattern) (ha : d128327 p = 1) (hb : d162092 p = 1) : d162617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16605 q = 1) (hb : d162092 q = 1) : d162584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16605, d162584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52443 q ha hb
    | true =>
      simp only [d16605, d162584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52444 q ha hb
  have h2 (q : Pattern) (ha : d128316 q = 1) (hb : d162092 q = 1) : d162585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128316, d162585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128316, d162585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16611 q = 1) (hb : d162092 q = 1) : d162587 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16611, d162587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52445 q ha hb
    | true =>
      simp only [d16611, d162587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16612 q = 1) (hb : d162092 q = 1) : d162588 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16612, d162588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16612, d162588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128317 q = 1) (hb : d162092 q = 1) : d162589 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128317, d162589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128317, d162589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128325 q = 1) (hb : d162092 q = 1) : d162615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128325, d162615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128325, d162615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128326 q = 1) (hb : d162092 q = 1) : d162616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128326, d162616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128326, d162616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128327 q = 1) (hb : d162092 q = 1) : d162617 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128327, d162617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128327, d162617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52448 (p : Pattern) (ha : d15024 p = 1) (hb : d162092 p = 1) : d6355 p = 1 := by
  have h0 (q : Pattern) (ha : d6354 q = 1) (hb : d162091 q = 1) : d6354 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15023 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15024 q = 1) (hb : d162092 q = 1) : d6355 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15024, d162092, d6355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15024, d162092, d6355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52449 (p : Pattern) (ha : d16655 p = 1) (hb : d162092 p = 1) : d162626 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1379 q = 1) : d1379 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16649 q = 1) (hb : d116750 q = 1) : d22028 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16649, d22028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16649, d22028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51710 q ha hb
  have h3 (q : Pattern) (ha : d9753 q = 1) (hb : d116750 q = 1) : d21737 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9753, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51710 q ha hb
    | true =>
      simp only [d9753, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16650 q = 1) (hb : d116750 q = 1) : d22029 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16650, d22029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16650, d22029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9755 q = 1) (hb : d116750 q = 1) : d21738 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9755, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9755, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d16651 q = 1) (hb : d116750 q = 1) : d22030 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16651, d22030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16651, d22030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16652 q = 1) (hb : d116750 q = 1) : d22031 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16652, d22031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16652, d22031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d16653 q = 1) (hb : d162091 q = 1) : d162625 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16653, d162091, d162625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16653, d162091, d162625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16654 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16655 q = 1) (hb : d162092 q = 1) : d162626 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16655, d162092, d162626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16655, d162092, d162626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro52450 (p : Pattern) (ha : d16662 p = 1) (hb : d162092 p = 1) : d162628 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1383 q = 1) : d1383 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16656 q = 1) (hb : d116750 q = 1) : d22043 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16656, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16656, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51685 q ha hb
  have h3 (q : Pattern) (ha : d9789 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51685 q ha hb
    | true =>
      simp only [d9789, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16657 q = 1) (hb : d116750 q = 1) : d22044 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16657, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16657, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9791 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9791, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9791, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d16658 q = 1) (hb : d116750 q = 1) : d22045 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16658, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16658, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16659 q = 1) (hb : d116750 q = 1) : d22046 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16659, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16659, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d16660 q = 1) (hb : d162091 q = 1) : d162627 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16660, d162091, d162627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16660, d162091, d162627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16661 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16662 q = 1) (hb : d162092 q = 1) : d162628 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16662, d162092, d162628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16662, d162092, d162628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro52451 (p : Pattern) (ha : d16667 p = 1) (hb : d162092 p = 1) : d13169 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d13163 q = 1) : d13163 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15004 q = 1) (hb : d116750 q = 1) : d13164 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d13164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15004, d13164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36939 q ha hb
  have h3 (q : Pattern) (ha : d9800 q = 1) (hb : d116750 q = 1) : d13025 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d13025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36939 q ha hb
    | true =>
      simp only [d9800, d13025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15005 q = 1) (hb : d116750 q = 1) : d13165 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d13165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15005, d13165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9802 q = 1) (hb : d116750 q = 1) : d13026 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d13026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9802, d13026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15006 q = 1) (hb : d116750 q = 1) : d13166 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15006, d13166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15006, d13166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15007 q = 1) (hb : d116750 q = 1) : d13167 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15007, d13167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15007, d13167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d16666 q = 1) (hb : d162091 q = 1) : d13168 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16666, d162091, d13168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16666, d162091, d13168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d15008 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16667 q = 1) (hb : d162092 q = 1) : d13169 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16667, d162092, d13169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16667, d162092, d13169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro52452 (p : Pattern) (ha : d16681 p = 1) (hb : d162092 p = 1) : d162646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16663 q = 1) (hb : d162092 q = 1) : d162629 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16663, d162629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52449 q ha hb
    | true =>
      simp only [d16663, d162629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52450 q ha hb
  have h2 (q : Pattern) (ha : d16664 q = 1) (hb : d162092 q = 1) : d162630 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16664, d162630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16664, d162630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16665 q = 1) (hb : d162092 q = 1) : d162631 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16665, d162631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16665, d162631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16668 q = 1) (hb : d162092 q = 1) : d162632 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16668, d162632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52450 q ha hb
    | true =>
      simp only [d16668, d162632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52451 q ha hb
  have h5 (q : Pattern) (ha : d16669 q = 1) (hb : d162092 q = 1) : d162633 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16669, d162633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16669, d162633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16670 q = 1) (hb : d162092 q = 1) : d162634 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16670, d162634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16670, d162634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16671 q = 1) (hb : d162092 q = 1) : d162635 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16671, d162635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16671, d162635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16673 q = 1) (hb : d162092 q = 1) : d162638 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52450 q ha hb
    | true =>
      simp only [d16673, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52424 q ha hb
  have h9 (q : Pattern) (ha : d16674 q = 1) (hb : d162092 q = 1) : d162639 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16675 q = 1) (hb : d162092 q = 1) : d162640 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16676 q = 1) (hb : d162092 q = 1) : d162641 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52424 q ha hb
    | true =>
      simp only [d16676, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52448 q ha hb
  have h12 (q : Pattern) (ha : d16677 q = 1) (hb : d162092 q = 1) : d162642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16678 q = 1) (hb : d162092 q = 1) : d162643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16679 q = 1) (hb : d162092 q = 1) : d162644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16679, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16680 q = 1) (hb : d162092 q = 1) : d162645 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16680, d162645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16680, d162645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16681 q = 1) (hb : d162092 q = 1) : d162646 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16681, d162646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16681, d162646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro52453 (p : Pattern) (ha : d16686 p = 1) (hb : d162092 p = 1) : d162651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d162092 q = 1) : d162638 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52450 q ha hb
    | true =>
      simp only [d16673, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52424 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d162092 q = 1) : d162639 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d162092 q = 1) : d162640 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d162092 q = 1) : d162641 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52424 q ha hb
    | true =>
      simp only [d16676, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52448 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d162092 q = 1) : d162642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d162092 q = 1) : d162643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d162092 q = 1) : d162644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16684 q = 1) (hb : d162092 q = 1) : d162649 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16684, d162649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16684, d162649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16685 q = 1) (hb : d162092 q = 1) : d162650 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16685, d162650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16685, d162650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16686 q = 1) (hb : d162092 q = 1) : d162651 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16686, d162651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16686, d162651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro52454 (p : Pattern) (ha : d16692 p = 1) (hb : d162092 p = 1) : d162657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16682 q = 1) (hb : d162092 q = 1) : d162647 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16682, d162647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52452 q ha hb
    | true =>
      simp only [d16682, d162647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16683 q = 1) (hb : d162092 q = 1) : d162648 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16683, d162648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16683, d162648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16687 q = 1) (hb : d162092 q = 1) : d162652 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16687, d162652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52453 q ha hb
    | true =>
      simp only [d16687, d162652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16688 q = 1) (hb : d162092 q = 1) : d162653 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16688, d162653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16688, d162653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16689 q = 1) (hb : d162092 q = 1) : d162654 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16689, d162654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16689, d162654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16690 q = 1) (hb : d162092 q = 1) : d162655 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16690, d162655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16690, d162655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16691 q = 1) (hb : d162092 q = 1) : d162656 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16691, d162656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16691, d162656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16692 q = 1) (hb : d162092 q = 1) : d162657 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16692, d162657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16692, d162657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52455 (p : Pattern) (ha : d16704 p = 1) (hb : d162092 p = 1) : d162669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16687 q = 1) (hb : d162092 q = 1) : d162652 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16687, d162652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52453 q ha hb
    | true =>
      simp only [d16687, d162652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16688 q = 1) (hb : d162092 q = 1) : d162653 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16688, d162653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16688, d162653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16699 q = 1) (hb : d162092 q = 1) : d162664 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d162664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52425 q ha hb
    | true =>
      simp only [d16699, d162664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16700 q = 1) (hb : d162092 q = 1) : d162665 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d162665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d162665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16701 q = 1) (hb : d162092 q = 1) : d162666 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16701, d162666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16701, d162666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16702 q = 1) (hb : d162092 q = 1) : d162667 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16702, d162667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16702, d162667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16703 q = 1) (hb : d162092 q = 1) : d162668 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16703, d162668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16703, d162668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16704 q = 1) (hb : d162092 q = 1) : d162669 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16704, d162669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16704, d162669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52456 (p : Pattern) (ha : d16748 p = 1) (hb : d162092 p = 1) : d162673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d162092 q = 1) : d162638 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52450 q ha hb
    | true =>
      simp only [d16673, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52424 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d162092 q = 1) : d162639 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d162092 q = 1) : d162640 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d162092 q = 1) : d162641 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52424 q ha hb
    | true =>
      simp only [d16676, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52448 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d162092 q = 1) : d162642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d162092 q = 1) : d162643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d162092 q = 1) : d162644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13190 q = 1) (hb : d162092 q = 1) : d13190 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d16743 q = 1) (hb : d162092 q = 1) : d162658 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16743, d162658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52424 q ha hb
    | true =>
      simp only [d16743, d162658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16744 q = 1) (hb : d162092 q = 1) : d162659 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16744, d162659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16744, d162659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16745 q = 1) (hb : d162092 q = 1) : d162660 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16745, d162660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16745, d162660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16746 q = 1) (hb : d162092 q = 1) : d162661 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16746, d162661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16746, d162661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16747 q = 1) (hb : d162092 q = 1) : d162672 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16747, d162672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16747, d162672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16748 q = 1) (hb : d162092 q = 1) : d162673 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16748, d162673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16748, d162673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro52457 (p : Pattern) (ha : d16754 p = 1) (hb : d162092 p = 1) : d162679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16749 q = 1) (hb : d162092 q = 1) : d162674 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16749, d162674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52456 q ha hb
    | true =>
      simp only [d16749, d162674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16750 q = 1) (hb : d162092 q = 1) : d162675 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16750, d162675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16750, d162675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16751 q = 1) (hb : d162092 q = 1) : d162676 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16751, d162676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16751, d162676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16752 q = 1) (hb : d162092 q = 1) : d162677 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16752, d162677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16752, d162677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16753 q = 1) (hb : d162092 q = 1) : d162678 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16753, d162678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16753, d162678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16754 q = 1) (hb : d162092 q = 1) : d162679 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16754, d162679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16754, d162679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52458 (p : Pattern) (ha : d128337 p = 1) (hb : d162092 p = 1) : d162685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16705 q = 1) (hb : d162092 q = 1) : d162670 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16705, d162670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52454 q ha hb
    | true =>
      simp only [d16705, d162670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52455 q ha hb
  have h2 (q : Pattern) (ha : d128333 q = 1) (hb : d162092 q = 1) : d162671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128333, d162671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128333, d162671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16755 q = 1) (hb : d162092 q = 1) : d162680 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16755, d162680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52457 q ha hb
    | true =>
      simp only [d16755, d162680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16756 q = 1) (hb : d162092 q = 1) : d162681 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16756, d162681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16756, d162681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128334 q = 1) (hb : d162092 q = 1) : d162682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128334, d162682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128334, d162682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128335 q = 1) (hb : d162092 q = 1) : d162683 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128335, d162683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128335, d162683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128336 q = 1) (hb : d162092 q = 1) : d162684 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128336, d162684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128336, d162684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128337 q = 1) (hb : d162092 q = 1) : d162685 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128337, d162685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128337, d162685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52459 (p : Pattern) (ha : d128343 p = 1) (hb : d162092 p = 1) : d162702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16477 q = 1) (hb : d162092 q = 1) : d162503 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16477, d162503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16477, d162503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52414 q ha hb
  have h2 (q : Pattern) (ha : d16478 q = 1) (hb : d162092 q = 1) : d162504 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16478, d162504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16478, d162504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16487 q = 1) (hb : d162092 q = 1) : d162513 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16487, d162513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52414 q ha hb
    | true =>
      simp only [d16487, d162513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52417 q ha hb
  have h4 (q : Pattern) (ha : d16488 q = 1) (hb : d162092 q = 1) : d162514 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16488, d162514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16488, d162514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16489 q = 1) (hb : d162092 q = 1) : d162515 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16489, d162515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16489, d162515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128321 q = 1) (hb : d162092 q = 1) : d162593 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128321, d162593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52438 q ha hb
    | true =>
      simp only [d128321, d162593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52446 q ha hb
  have h7 (q : Pattern) (ha : d16635 q = 1) (hb : d162092 q = 1) : d162611 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16635, d162611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52420 q ha hb
    | true =>
      simp only [d16635, d162611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52421 q ha hb
  have h8 (q : Pattern) (ha : d128322 q = 1) (hb : d162092 q = 1) : d162612 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128322, d162612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128322, d162612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128323 q = 1) (hb : d162092 q = 1) : d162613 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128323, d162613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128323, d162613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128324 q = 1) (hb : d162092 q = 1) : d162614 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128324, d162614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128324, d162614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128328 q = 1) (hb : d162092 q = 1) : d162618 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128328, d162618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128328, d162618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52447 q ha hb
  have h12 (q : Pattern) (ha : d16644 q = 1) (hb : d162092 q = 1) : d162620 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16644, d162620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16644, d162620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52422 q ha hb
  have h13 (q : Pattern) (ha : d128329 q = 1) (hb : d162092 q = 1) : d162621 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128329, d162621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128329, d162621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128330 q = 1) (hb : d162092 q = 1) : d162622 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128330, d162622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128330, d162622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128331 q = 1) (hb : d162092 q = 1) : d162623 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128331, d162623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128331, d162623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128332 q = 1) (hb : d162092 q = 1) : d162624 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128332, d162624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128332, d162624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128338 q = 1) (hb : d162092 q = 1) : d162686 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128338, d162686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128338, d162686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52458 q ha hb
  have h18 (q : Pattern) (ha : d16772 q = 1) (hb : d162092 q = 1) : d162697 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16772, d162697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16772, d162697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52427 q ha hb
  have h19 (q : Pattern) (ha : d128339 q = 1) (hb : d162092 q = 1) : d162698 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128339, d162698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128339, d162698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128340 q = 1) (hb : d162092 q = 1) : d162699 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128340, d162699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128340, d162699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128341 q = 1) (hb : d162092 q = 1) : d162700 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128341, d162700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128341, d162700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128342 q = 1) (hb : d162092 q = 1) : d162701 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128342, d162701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128342, d162701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128343 q = 1) (hb : d162092 q = 1) : d162702 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128343, d162702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128343, d162702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro52460 (p : Pattern) (ha : d128349 p = 1) (hb : d162092 p = 1) : d162708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128344 q = 1) (hb : d162092 q = 1) : d162703 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128344, d162703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128344, d162703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52459 q ha hb
  have h2 (q : Pattern) (ha : d128345 q = 1) (hb : d162092 q = 1) : d162704 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128345, d162704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128345, d162704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128346 q = 1) (hb : d162092 q = 1) : d162705 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128346, d162705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128346, d162705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128347 q = 1) (hb : d162092 q = 1) : d162706 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128347, d162706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128347, d162706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128348 q = 1) (hb : d162092 q = 1) : d162707 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128348, d162707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128348, d162707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128349 q = 1) (hb : d162092 q = 1) : d162708 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128349, d162708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128349, d162708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52461 (p : Pattern) (ha : d15166 p = 1) (hb : d162092 p = 1) : d5139 p = 1 := by
  have h0 (q : Pattern) (ha : d5138 q = 1) (hb : d162091 q = 1) : d5138 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15165 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15166 q = 1) (hb : d162092 q = 1) : d5139 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15166, d162092, d5139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15166, d162092, d5139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52462 (p : Pattern) (ha : d15171 p = 1) (hb : d162092 p = 1) : d13287 p = 1 := by
  have h0 (q : Pattern) (ha : d1588 q = 1) (hb : d162091 q = 1) : d1588 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15165 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15171 q = 1) (hb : d162092 q = 1) : d13287 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15171, d162092, d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15171, d162092, d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52463 (p : Pattern) (ha : d16791 p = 1) (hb : d162092 p = 1) : d162713 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1558 q = 1) : d1558 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10074 q = 1) (hb : d116750 q = 1) : d22220 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10074, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51744 q ha hb
    | true =>
      simp only [d10074, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10076 q = 1) (hb : d116750 q = 1) : d22221 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10076, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10076, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16787 q = 1) (hb : d116750 q = 1) : d22222 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16787, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16787, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16788 q = 1) (hb : d116750 q = 1) : d22223 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16788, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16788, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d16789 q = 1) (hb : d162091 q = 1) : d162712 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16789, d162091, d162712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16789, d162091, d162712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d16790 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d16791 q = 1) (hb : d162092 q = 1) : d162713 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16791, d162092, d162713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16791, d162092, d162713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro52464 (p : Pattern) (ha : d16795 p = 1) (hb : d162092 p = 1) : d162715 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1573 q = 1) : d1573 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10115 q = 1) (hb : d116750 q = 1) : d22233 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51746 q ha hb
    | true =>
      simp only [d10115, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10117 q = 1) (hb : d116750 q = 1) : d22234 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10117, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10117, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16792 q = 1) (hb : d116750 q = 1) : d22235 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16792, d22235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16792, d22235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16793 q = 1) (hb : d116750 q = 1) : d22236 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16793, d22236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16793, d22236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d16794 q = 1) (hb : d162091 q = 1) : d162714 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16794, d162091, d162714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16794, d162091, d162714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d15158 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d16795 q = 1) (hb : d162092 q = 1) : d162715 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16795, d162092, d162715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16795, d162092, d162715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro52465 (p : Pattern) (ha : d16808 p = 1) (hb : d162092 p = 1) : d162728 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d162092 q = 1) : d162716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52463 q ha hb
    | true =>
      simp only [d16796, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52464 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d162092 q = 1) : d162717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d162092 q = 1) : d162718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16799 q = 1) (hb : d162092 q = 1) : d162719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52464 q ha hb
    | true =>
      simp only [d16799, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52461 q ha hb
  have h5 (q : Pattern) (ha : d16800 q = 1) (hb : d162092 q = 1) : d162720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16801 q = 1) (hb : d162092 q = 1) : d162721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16802 q = 1) (hb : d162092 q = 1) : d162722 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16803 q = 1) (hb : d162092 q = 1) : d162723 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, d162723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52464 q ha hb
    | true =>
      simp only [d16803, d162723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52462 q ha hb
  have h9 (q : Pattern) (ha : d16804 q = 1) (hb : d162092 q = 1) : d162724 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16804, d162724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16804, d162724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16805 q = 1) (hb : d162092 q = 1) : d162725 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16805, d162725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16805, d162725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16806 q = 1) (hb : d162092 q = 1) : d162726 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16806, d162726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16806, d162726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16807 q = 1) (hb : d162092 q = 1) : d162727 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16807, d162727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16807, d162727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16808 q = 1) (hb : d162092 q = 1) : d162728 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16808, d162728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16808, d162728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro52466 (p : Pattern) (ha : d16812 p = 1) (hb : d162092 p = 1) : d162732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16803 q = 1) (hb : d162092 q = 1) : d162723 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, d162723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52464 q ha hb
    | true =>
      simp only [d16803, d162723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52462 q ha hb
  have h2 (q : Pattern) (ha : d16804 q = 1) (hb : d162092 q = 1) : d162724 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16804, d162724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16804, d162724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16805 q = 1) (hb : d162092 q = 1) : d162725 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16805, d162725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16805, d162725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16806 q = 1) (hb : d162092 q = 1) : d162726 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16806, d162726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16806, d162726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16811 q = 1) (hb : d162092 q = 1) : d162731 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16811, d162731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16811, d162731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16812 q = 1) (hb : d162092 q = 1) : d162732 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16812, d162732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16812, d162732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52467 (p : Pattern) (ha : d16818 p = 1) (hb : d162092 p = 1) : d162738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d162092 q = 1) : d162729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52465 q ha hb
    | true =>
      simp only [d16809, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d162092 q = 1) : d162730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52466 q ha hb
    | true =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d162092 q = 1) : d162735 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d162092 q = 1) : d162736 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16817 q = 1) (hb : d162092 q = 1) : d162737 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16817, d162737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16817, d162737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16818 q = 1) (hb : d162092 q = 1) : d162738 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16818, d162738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16818, d162738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52468 (p : Pattern) (ha : d16822 p = 1) (hb : d162092 p = 1) : d162742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52466 q ha hb
    | true =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d162092 q = 1) : d162739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d162092 q = 1) : d162740 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16821 q = 1) (hb : d162092 q = 1) : d162741 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16821, d162741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16821, d162741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16822 q = 1) (hb : d162092 q = 1) : d162742 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16822, d162742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16822, d162742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52469 (p : Pattern) (ha : d16828 p = 1) (hb : d162092 p = 1) : d162748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16823 q = 1) (hb : d162092 q = 1) : d162743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16823, d162743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52467 q ha hb
    | true =>
      simp only [d16823, d162743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52468 q ha hb
  have h2 (q : Pattern) (ha : d16824 q = 1) (hb : d162092 q = 1) : d162744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16824, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16824, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16825 q = 1) (hb : d162092 q = 1) : d162745 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16825, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16825, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16826 q = 1) (hb : d162092 q = 1) : d162746 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16826, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16826, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16827 q = 1) (hb : d162092 q = 1) : d162747 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16827, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16827, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16828 q = 1) (hb : d162092 q = 1) : d162748 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16828, d162748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16828, d162748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52470 (p : Pattern) (ha : d16831 p = 1) (hb : d162092 p = 1) : d162751 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d162092 q = 1) : d162729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52465 q ha hb
    | true =>
      simp only [d16809, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d162092 q = 1) : d162730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52466 q ha hb
    | true =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d162092 q = 1) : d162735 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d162092 q = 1) : d162736 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16817 q = 1) (hb : d162092 q = 1) : d162737 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16817, d162737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16817, d162737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16831 q = 1) (hb : d162092 q = 1) : d162751 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16831, d162751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16831, d162751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52471 (p : Pattern) (ha : d16832 p = 1) (hb : d162092 p = 1) : d162752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52466 q ha hb
    | true =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d162092 q = 1) : d162739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d162092 q = 1) : d162740 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16821 q = 1) (hb : d162092 q = 1) : d162741 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16821, d162741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16821, d162741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16832 q = 1) (hb : d162092 q = 1) : d162752 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16832, d162752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16832, d162752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52472 (p : Pattern) (ha : d16838 p = 1) (hb : d162092 p = 1) : d162758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16823 q = 1) (hb : d162092 q = 1) : d162743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16823, d162743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52467 q ha hb
    | true =>
      simp only [d16823, d162743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52468 q ha hb
  have h2 (q : Pattern) (ha : d16824 q = 1) (hb : d162092 q = 1) : d162744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16824, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16824, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16825 q = 1) (hb : d162092 q = 1) : d162745 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16825, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16825, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16826 q = 1) (hb : d162092 q = 1) : d162746 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16826, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16826, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16827 q = 1) (hb : d162092 q = 1) : d162747 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16827, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16827, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16833 q = 1) (hb : d162092 q = 1) : d162753 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16833, d162753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52470 q ha hb
    | true =>
      simp only [d16833, d162753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52471 q ha hb
  have h7 (q : Pattern) (ha : d16834 q = 1) (hb : d162092 q = 1) : d162754 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16834, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16834, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16835 q = 1) (hb : d162092 q = 1) : d162755 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16835, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16835, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16836 q = 1) (hb : d162092 q = 1) : d162756 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16836, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16836, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16837 q = 1) (hb : d162092 q = 1) : d162757 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16837, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16837, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16838 q = 1) (hb : d162092 q = 1) : d162758 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16838, d162758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16838, d162758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52473 (p : Pattern) (ha : d16879 p = 1) (hb : d162092 p = 1) : d162793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d162092 q = 1) : d162716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52463 q ha hb
    | true =>
      simp only [d16796, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52464 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d162092 q = 1) : d162717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d162092 q = 1) : d162718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16799 q = 1) (hb : d162092 q = 1) : d162719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52464 q ha hb
    | true =>
      simp only [d16799, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52461 q ha hb
  have h5 (q : Pattern) (ha : d16800 q = 1) (hb : d162092 q = 1) : d162720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16801 q = 1) (hb : d162092 q = 1) : d162721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16802 q = 1) (hb : d162092 q = 1) : d162722 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16877 q = 1) (hb : d162092 q = 1) : d162791 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16877, d162791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16877, d162791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16878 q = 1) (hb : d162092 q = 1) : d162792 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16878, d162792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16878, d162792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16879 q = 1) (hb : d162092 q = 1) : d162793 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16879, d162793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16879, d162793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro52474 (p : Pattern) (ha : d16889 p = 1) (hb : d162092 p = 1) : d162803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16880 q = 1) (hb : d162092 q = 1) : d162794 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52473 q ha hb
    | true =>
      simp only [d16880, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16881 q = 1) (hb : d162092 q = 1) : d162795 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52466 q ha hb
    | true =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16886 q = 1) (hb : d162092 q = 1) : d162800 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16886, d162800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16886, d162800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16887 q = 1) (hb : d162092 q = 1) : d162801 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16887, d162801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16887, d162801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16888 q = 1) (hb : d162092 q = 1) : d162802 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16888, d162802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16888, d162802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16889 q = 1) (hb : d162092 q = 1) : d162803 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16889, d162803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16889, d162803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52475 (p : Pattern) (ha : d16983 p = 1) (hb : d162092 p = 1) : d162849 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16973 q = 1) (hb : d162092 q = 1) : d162839 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16973, d162839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52474 q ha hb
    | true =>
      simp only [d16973, d162839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52468 q ha hb
  have h2 (q : Pattern) (ha : d16974 q = 1) (hb : d162092 q = 1) : d162840 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16974, d162840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16974, d162840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16975 q = 1) (hb : d162092 q = 1) : d162841 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16975, d162841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16975, d162841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16976 q = 1) (hb : d162092 q = 1) : d162842 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16976, d162842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16976, d162842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16977 q = 1) (hb : d162092 q = 1) : d162843 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16977, d162843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16977, d162843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16978 q = 1) (hb : d162092 q = 1) : d162844 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16978, d162844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52468 q ha hb
    | true =>
      simp only [d16978, d162844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16979 q = 1) (hb : d162092 q = 1) : d162845 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16979, d162845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16979, d162845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16980 q = 1) (hb : d162092 q = 1) : d162846 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16980, d162846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16980, d162846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16981 q = 1) (hb : d162092 q = 1) : d162847 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16981, d162847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16981, d162847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16982 q = 1) (hb : d162092 q = 1) : d162848 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16982, d162848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16982, d162848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16983 q = 1) (hb : d162092 q = 1) : d162849 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16983, d162849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16983, d162849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52476 (p : Pattern) (ha : d16989 p = 1) (hb : d162092 p = 1) : d162855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16978 q = 1) (hb : d162092 q = 1) : d162844 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16978, d162844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52468 q ha hb
    | true =>
      simp only [d16978, d162844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16979 q = 1) (hb : d162092 q = 1) : d162845 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16979, d162845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16979, d162845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16980 q = 1) (hb : d162092 q = 1) : d162846 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16980, d162846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16980, d162846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16981 q = 1) (hb : d162092 q = 1) : d162847 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16981, d162847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16981, d162847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16982 q = 1) (hb : d162092 q = 1) : d162848 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16982, d162848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16982, d162848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16984 q = 1) (hb : d162092 q = 1) : d162850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16984, d162850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52471 q ha hb
    | true =>
      simp only [d16984, d162850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16985 q = 1) (hb : d162092 q = 1) : d162851 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16985, d162851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16985, d162851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16986 q = 1) (hb : d162092 q = 1) : d162852 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16986, d162852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16986, d162852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16987 q = 1) (hb : d162092 q = 1) : d162853 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16987, d162853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16987, d162853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16988 q = 1) (hb : d162092 q = 1) : d162854 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16988, d162854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16988, d162854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16989 q = 1) (hb : d162092 q = 1) : d162855 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16989, d162855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16989, d162855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52477 (p : Pattern) (ha : d16998 p = 1) (hb : d162092 p = 1) : d162864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16984 q = 1) (hb : d162092 q = 1) : d162850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16984, d162850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52471 q ha hb
    | true =>
      simp only [d16984, d162850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16985 q = 1) (hb : d162092 q = 1) : d162851 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16985, d162851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16985, d162851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16986 q = 1) (hb : d162092 q = 1) : d162852 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16986, d162852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16986, d162852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16987 q = 1) (hb : d162092 q = 1) : d162853 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16987, d162853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16987, d162853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16988 q = 1) (hb : d162092 q = 1) : d162854 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16988, d162854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16988, d162854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16998 q = 1) (hb : d162092 q = 1) : d162864 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16998, d162864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16998, d162864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52478 (p : Pattern) (ha : d15435 p = 1) (hb : d162092 p = 1) : d13516 p = 1 := by
  have h0 (q : Pattern) (ha : d1877 q = 1) (hb : d162091 q = 1) : d1877 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15416 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15435 q = 1) (hb : d162092 q = 1) : d13516 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15435, d162092, d13516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15435, d162092, d13516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52479 (p : Pattern) (ha : d17032 p = 1) (hb : d162092 p = 1) : d162881 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1865 q = 1) : d1865 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17027 q = 1) (hb : d116750 q = 1) : d22529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17027, d22529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17027, d22529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51746 q ha hb
  have h3 (q : Pattern) (ha : d10115 q = 1) (hb : d116750 q = 1) : d22233 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51746 q ha hb
    | true =>
      simp only [d10115, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d17028 q = 1) (hb : d116750 q = 1) : d22530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17028, d22530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17028, d22530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10117 q = 1) (hb : d116750 q = 1) : d22234 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10117, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10117, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d17029 q = 1) (hb : d116750 q = 1) : d22531 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17029, d22531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17029, d22531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17030 q = 1) (hb : d116750 q = 1) : d22532 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17030, d22532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17030, d22532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d17031 q = 1) (hb : d162091 q = 1) : d162880 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17031, d162091, d162880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17031, d162091, d162880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d15401 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17032 q = 1) (hb : d162092 q = 1) : d162881 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17032, d162092, d162881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17032, d162092, d162881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro52480 (p : Pattern) (ha : d17058 p = 1) (hb : d162092 p = 1) : d162907 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17053 q = 1) (hb : d162092 q = 1) : d162902 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d162902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52479 q ha hb
    | true =>
      simp only [d17053, d162902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52478 q ha hb
  have h2 (q : Pattern) (ha : d17054 q = 1) (hb : d162092 q = 1) : d162903 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d162903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17054, d162903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17055 q = 1) (hb : d162092 q = 1) : d162904 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d162904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, d162904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17056 q = 1) (hb : d162092 q = 1) : d162905 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d162905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17056, d162905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17057 q = 1) (hb : d162092 q = 1) : d162906 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17057, d162906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17057, d162906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17058 q = 1) (hb : d162092 q = 1) : d162907 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17058, d162907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17058, d162907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52481 (p : Pattern) (ha : d17130 p = 1) (hb : d162092 p = 1) : d162934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17059 q = 1) (hb : d162092 q = 1) : d162908 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17059, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52480 q ha hb
    | true =>
      simp only [d17059, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17060 q = 1) (hb : d162092 q = 1) : d162909 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17060, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17060, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17127 q = 1) (hb : d162092 q = 1) : d162931 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17127, d162931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17127, d162931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17128 q = 1) (hb : d162092 q = 1) : d162932 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17128, d162932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17128, d162932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17129 q = 1) (hb : d162092 q = 1) : d162933 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17129, d162933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17129, d162933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17130 q = 1) (hb : d162092 q = 1) : d162934 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17130, d162934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17130, d162934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52482 (p : Pattern) (ha : d17136 p = 1) (hb : d162092 p = 1) : d162940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17131 q = 1) (hb : d162092 q = 1) : d162935 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17131, d162935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52481 q ha hb
    | true =>
      simp only [d17131, d162935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17132 q = 1) (hb : d162092 q = 1) : d162936 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17132, d162936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17132, d162936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17133 q = 1) (hb : d162092 q = 1) : d162937 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17133, d162937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17133, d162937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17134 q = 1) (hb : d162092 q = 1) : d162938 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17134, d162938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17134, d162938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17135 q = 1) (hb : d162092 q = 1) : d162939 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17135, d162939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17135, d162939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17136 q = 1) (hb : d162092 q = 1) : d162940 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17136, d162940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17136, d162940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52483 (p : Pattern) (ha : d16843 p = 1) (hb : d162092 p = 1) : d162763 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d162092 q = 1) : d162729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52465 q ha hb
    | true =>
      simp only [d16809, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d162092 q = 1) : d162730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52466 q ha hb
    | true =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d162092 q = 1) : d162735 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d162092 q = 1) : d162736 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16842 q = 1) (hb : d162092 q = 1) : d162762 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16842, d162762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16842, d162762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16843 q = 1) (hb : d162092 q = 1) : d162763 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16843, d162763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16843, d162763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52484 (p : Pattern) (ha : d16845 p = 1) (hb : d162092 p = 1) : d162765 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52466 q ha hb
    | true =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d162092 q = 1) : d162739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d162092 q = 1) : d162740 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16844 q = 1) (hb : d162092 q = 1) : d162764 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16844, d162764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16844, d162764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16845 q = 1) (hb : d162092 q = 1) : d162765 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16845, d162765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16845, d162765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52485 (p : Pattern) (ha : d16852 p = 1) (hb : d162092 p = 1) : d162772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d162092 q = 1) : d162729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52465 q ha hb
    | true =>
      simp only [d16809, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d162092 q = 1) : d162730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52466 q ha hb
    | true =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d162092 q = 1) : d162735 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16850 q = 1) (hb : d162092 q = 1) : d162770 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16850, d162770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16850, d162770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16851 q = 1) (hb : d162092 q = 1) : d162771 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16851, d162771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16851, d162771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16852 q = 1) (hb : d162092 q = 1) : d162772 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16852, d162772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16852, d162772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52486 (p : Pattern) (ha : d16855 p = 1) (hb : d162092 p = 1) : d162775 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52466 q ha hb
    | true =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d162092 q = 1) : d162739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16853 q = 1) (hb : d162092 q = 1) : d162773 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16853, d162773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16853, d162773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16854 q = 1) (hb : d162092 q = 1) : d162774 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16854, d162774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16854, d162774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16855 q = 1) (hb : d162092 q = 1) : d162775 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16855, d162775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16855, d162775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52487 (p : Pattern) (ha : d16863 p = 1) (hb : d162092 p = 1) : d162779 p = 1 := by
  have h0 (q : Pattern) (ha : d16861 q = 1) (hb : d162091 q = 1) : d16861 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16862 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16863 q = 1) (hb : d162092 q = 1) : d162779 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16863, d162092, d162779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16863, d162092, d162779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52488 (p : Pattern) (ha : d16868 p = 1) (hb : d162092 p = 1) : d13356 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d13349 q = 1) : d13349 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10085 q = 1) (hb : d116750 q = 1) : d13351 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d13351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36999 q ha hb
    | true =>
      simp only [d10085, d13351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10087 q = 1) (hb : d116750 q = 1) : d13352 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d13352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10087, d13352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15156 q = 1) (hb : d116750 q = 1) : d13353 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d13353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15156, d13353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15157 q = 1) (hb : d116750 q = 1) : d13354 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d13354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15157, d13354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d16867 q = 1) (hb : d162091 q = 1) : d13355 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16867, d162091, d13355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16867, d162091, d13355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d15158 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d16868 q = 1) (hb : d162092 q = 1) : d13356 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16868, d162092, d13356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16868, d162092, d13356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro52489 (p : Pattern) (ha : d16874 p = 1) (hb : d162092 p = 1) : d162788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16864 q = 1) (hb : d162092 q = 1) : d162780 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16864, d162780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52487 q ha hb
    | true =>
      simp only [d16864, d162780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52463 q ha hb
  have h2 (q : Pattern) (ha : d16865 q = 1) (hb : d162092 q = 1) : d162781 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16865, d162781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16865, d162781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16866 q = 1) (hb : d162092 q = 1) : d162782 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16866, d162782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16866, d162782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16869 q = 1) (hb : d162092 q = 1) : d162783 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16869, d162783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52463 q ha hb
    | true =>
      simp only [d16869, d162783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52488 q ha hb
  have h5 (q : Pattern) (ha : d16870 q = 1) (hb : d162092 q = 1) : d162784 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16870, d162784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16870, d162784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16871 q = 1) (hb : d162092 q = 1) : d162785 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16871, d162785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16871, d162785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16872 q = 1) (hb : d162092 q = 1) : d162786 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16872, d162786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16872, d162786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16796 q = 1) (hb : d162092 q = 1) : d162716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52463 q ha hb
    | true =>
      simp only [d16796, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52464 q ha hb
  have h9 (q : Pattern) (ha : d16797 q = 1) (hb : d162092 q = 1) : d162717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16798 q = 1) (hb : d162092 q = 1) : d162718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16799 q = 1) (hb : d162092 q = 1) : d162719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52464 q ha hb
    | true =>
      simp only [d16799, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52461 q ha hb
  have h12 (q : Pattern) (ha : d16800 q = 1) (hb : d162092 q = 1) : d162720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16801 q = 1) (hb : d162092 q = 1) : d162721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16802 q = 1) (hb : d162092 q = 1) : d162722 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16802, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16873 q = 1) (hb : d162092 q = 1) : d162787 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16873, d162787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16873, d162787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16874 q = 1) (hb : d162092 q = 1) : d162788 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16874, d162788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16874, d162788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro52490 (p : Pattern) (ha : d16885 p = 1) (hb : d162092 p = 1) : d162799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16875 q = 1) (hb : d162092 q = 1) : d162789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16875, d162789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52489 q ha hb
    | true =>
      simp only [d16875, d162789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16876 q = 1) (hb : d162092 q = 1) : d162790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16876, d162790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16876, d162790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16880 q = 1) (hb : d162092 q = 1) : d162794 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52473 q ha hb
    | true =>
      simp only [d16880, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16881 q = 1) (hb : d162092 q = 1) : d162795 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16882 q = 1) (hb : d162092 q = 1) : d162796 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16882, d162796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16882, d162796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16883 q = 1) (hb : d162092 q = 1) : d162797 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16883, d162797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16883, d162797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16884 q = 1) (hb : d162092 q = 1) : d162798 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16884, d162798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16884, d162798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16885 q = 1) (hb : d162092 q = 1) : d162799 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16885, d162799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16885, d162799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52491 (p : Pattern) (ha : d16934 p = 1) (hb : d162092 p = 1) : d162728 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d162092 q = 1) : d162716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52463 q ha hb
    | true =>
      simp only [d16796, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52464 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d162092 q = 1) : d162717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d162092 q = 1) : d162718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16799 q = 1) (hb : d162092 q = 1) : d162719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52464 q ha hb
    | true =>
      simp only [d16799, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52461 q ha hb
  have h5 (q : Pattern) (ha : d16800 q = 1) (hb : d162092 q = 1) : d162720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16801 q = 1) (hb : d162092 q = 1) : d162721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16802 q = 1) (hb : d162092 q = 1) : d162722 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13287 q = 1) (hb : d162092 q = 1) : d13287 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d16929 q = 1) (hb : d162092 q = 1) : d162723 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16929, d162723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52464 q ha hb
    | true =>
      simp only [d16929, d162723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16930 q = 1) (hb : d162092 q = 1) : d162724 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16930, d162724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16930, d162724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16931 q = 1) (hb : d162092 q = 1) : d162725 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16931, d162725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16931, d162725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16932 q = 1) (hb : d162092 q = 1) : d162726 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16932, d162726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16932, d162726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16933 q = 1) (hb : d162092 q = 1) : d162727 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16933, d162727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16933, d162727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16934 q = 1) (hb : d162092 q = 1) : d162728 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16934, d162728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16934, d162728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro52492 (p : Pattern) (ha : d16940 p = 1) (hb : d162092 p = 1) : d162809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16935 q = 1) (hb : d162092 q = 1) : d162729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16935, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52491 q ha hb
    | true =>
      simp only [d16935, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16936 q = 1) (hb : d162092 q = 1) : d162730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16936, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16936, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16937 q = 1) (hb : d162092 q = 1) : d162806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16937, d162806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16937, d162806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16938 q = 1) (hb : d162092 q = 1) : d162807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16938, d162807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16938, d162807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16939 q = 1) (hb : d162092 q = 1) : d162808 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16939, d162808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16939, d162808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16940 q = 1) (hb : d162092 q = 1) : d162809 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16940, d162809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16940, d162809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52493 (p : Pattern) (ha : d128357 p = 1) (hb : d162092 p = 1) : d162815 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16846 q = 1) (hb : d162092 q = 1) : d162766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16846, d162766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52483 q ha hb
    | true =>
      simp only [d16846, d162766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52484 q ha hb
  have h2 (q : Pattern) (ha : d16847 q = 1) (hb : d162092 q = 1) : d162767 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16847, d162767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16847, d162767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16848 q = 1) (hb : d162092 q = 1) : d162768 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16848, d162768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16848, d162768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16849 q = 1) (hb : d162092 q = 1) : d162769 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16849, d162769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16849, d162769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16856 q = 1) (hb : d162092 q = 1) : d162776 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16856, d162776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52485 q ha hb
    | true =>
      simp only [d16856, d162776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52486 q ha hb
  have h6 (q : Pattern) (ha : d16857 q = 1) (hb : d162092 q = 1) : d162777 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16857, d162777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16857, d162777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16858 q = 1) (hb : d162092 q = 1) : d162778 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16858, d162778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16858, d162778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16890 q = 1) (hb : d162092 q = 1) : d162804 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16890, d162804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52490 q ha hb
    | true =>
      simp only [d16890, d162804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52474 q ha hb
  have h9 (q : Pattern) (ha : d128353 q = 1) (hb : d162092 q = 1) : d162805 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128353, d162805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128353, d162805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16941 q = 1) (hb : d162092 q = 1) : d162810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16941, d162810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52492 q ha hb
    | true =>
      simp only [d16941, d162810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16942 q = 1) (hb : d162092 q = 1) : d162811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16942, d162811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16942, d162811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128354 q = 1) (hb : d162092 q = 1) : d162812 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128354, d162812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128354, d162812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128355 q = 1) (hb : d162092 q = 1) : d162813 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128355, d162813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128355, d162813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128356 q = 1) (hb : d162092 q = 1) : d162814 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128356, d162814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128356, d162814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128357 q = 1) (hb : d162092 q = 1) : d162815 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128357, d162815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128357, d162815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro52494 (p : Pattern) (ha : d16947 p = 1) (hb : d162092 p = 1) : d162816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d162092 q = 1) : d162729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52465 q ha hb
    | true =>
      simp only [d16809, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d162092 q = 1) : d162730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52466 q ha hb
    | true =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d162092 q = 1) : d162735 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d162092 q = 1) : d162736 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16842 q = 1) (hb : d162092 q = 1) : d162762 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16842, d162762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16842, d162762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16947 q = 1) (hb : d162092 q = 1) : d162816 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16947, d162816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16947, d162816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52495 (p : Pattern) (ha : d16948 p = 1) (hb : d162092 p = 1) : d162817 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52466 q ha hb
    | true =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d162092 q = 1) : d162739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d162092 q = 1) : d162740 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16844 q = 1) (hb : d162092 q = 1) : d162764 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16844, d162764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16844, d162764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16948 q = 1) (hb : d162092 q = 1) : d162817 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16948, d162817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16948, d162817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52496 (p : Pattern) (ha : d16953 p = 1) (hb : d162092 p = 1) : d162822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d162092 q = 1) : d162729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52465 q ha hb
    | true =>
      simp only [d16809, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d162092 q = 1) : d162730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52466 q ha hb
    | true =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d162092 q = 1) : d162735 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16850 q = 1) (hb : d162092 q = 1) : d162770 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16850, d162770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16850, d162770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16851 q = 1) (hb : d162092 q = 1) : d162771 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16851, d162771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16851, d162771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16953 q = 1) (hb : d162092 q = 1) : d162822 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16953, d162822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16953, d162822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52497 (p : Pattern) (ha : d16954 p = 1) (hb : d162092 p = 1) : d162823 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52466 q ha hb
    | true =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d162092 q = 1) : d162739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16853 q = 1) (hb : d162092 q = 1) : d162773 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16853, d162773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16853, d162773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16854 q = 1) (hb : d162092 q = 1) : d162774 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16854, d162774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16854, d162774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16954 q = 1) (hb : d162092 q = 1) : d162823 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16954, d162823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16954, d162823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52498 (p : Pattern) (ha : d16958 p = 1) (hb : d162092 p = 1) : d162827 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16875 q = 1) (hb : d162092 q = 1) : d162789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16875, d162789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52489 q ha hb
    | true =>
      simp only [d16875, d162789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16876 q = 1) (hb : d162092 q = 1) : d162790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16876, d162790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16876, d162790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16880 q = 1) (hb : d162092 q = 1) : d162794 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52473 q ha hb
    | true =>
      simp only [d16880, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16881 q = 1) (hb : d162092 q = 1) : d162795 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16882 q = 1) (hb : d162092 q = 1) : d162796 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16882, d162796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16882, d162796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16883 q = 1) (hb : d162092 q = 1) : d162797 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16883, d162797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16883, d162797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16884 q = 1) (hb : d162092 q = 1) : d162798 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16884, d162798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16884, d162798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16958 q = 1) (hb : d162092 q = 1) : d162827 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16958, d162827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16958, d162827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52499 (p : Pattern) (ha : d16959 p = 1) (hb : d162092 p = 1) : d162828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16880 q = 1) (hb : d162092 q = 1) : d162794 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52473 q ha hb
    | true =>
      simp only [d16880, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16881 q = 1) (hb : d162092 q = 1) : d162795 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52466 q ha hb
    | true =>
      simp only [d16813, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16886 q = 1) (hb : d162092 q = 1) : d162800 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16886, d162800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16886, d162800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16887 q = 1) (hb : d162092 q = 1) : d162801 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16887, d162801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16887, d162801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16888 q = 1) (hb : d162092 q = 1) : d162802 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16888, d162802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16888, d162802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16959 q = 1) (hb : d162092 q = 1) : d162828 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16959, d162828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16959, d162828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
