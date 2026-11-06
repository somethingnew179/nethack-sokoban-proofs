import NetHack.Soko22Hazard87.AndIntroBlocks0191
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro48000 (p : Pattern) (ha : d21444 p = 1) (hb : d202307 p = 1) : d206270 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d202307 q = 1) : d206261 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47998 q ha hb
    | true =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d202307 q = 1) : d206262 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d202307 q = 1) : d206267 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d206267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d206267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d202307 q = 1) : d206268 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d206268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d206268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21443 q = 1) (hb : d202307 q = 1) : d206269 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21443, d206269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21443, d206269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21444 q = 1) (hb : d202307 q = 1) : d206270 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21444, d206270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21444, d206270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48001 (p : Pattern) (ha : d21450 p = 1) (hb : d202307 p = 1) : d206276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21445 q = 1) (hb : d202307 q = 1) : d206271 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21445, d206271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47999 q ha hb
    | true =>
      simp only [d21445, d206271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48000 q ha hb
  have h2 (q : Pattern) (ha : d21446 q = 1) (hb : d202307 q = 1) : d206272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d206272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21446, d206272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21447 q = 1) (hb : d202307 q = 1) : d206273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d206273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21447, d206273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21448 q = 1) (hb : d202307 q = 1) : d206274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d206274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21448, d206274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21449 q = 1) (hb : d202307 q = 1) : d206275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d206275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21449, d206275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21450 q = 1) (hb : d202307 q = 1) : d206276 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21450, d206276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21450, d206276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48002 (p : Pattern) (ha : d21453 p = 1) (hb : d202307 p = 1) : d206279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d202307 q = 1) : d206257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d206257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47997 q ha hb
    | true =>
      simp only [d21431, d206257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d202307 q = 1) : d206258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d206258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d206258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d202307 q = 1) : d206261 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47998 q ha hb
    | true =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d202307 q = 1) : d206262 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d202307 q = 1) : d206263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d206263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d206263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d202307 q = 1) : d206264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d206264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d206264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21439 q = 1) (hb : d202307 q = 1) : d206265 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21439, d206265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21439, d206265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21453 q = 1) (hb : d202307 q = 1) : d206279 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21453, d206279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21453, d206279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48003 (p : Pattern) (ha : d21454 p = 1) (hb : d202307 p = 1) : d206280 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d202307 q = 1) : d206261 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47998 q ha hb
    | true =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d202307 q = 1) : d206262 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d202307 q = 1) : d206267 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d206267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d206267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d202307 q = 1) : d206268 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d206268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d206268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21443 q = 1) (hb : d202307 q = 1) : d206269 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21443, d206269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21443, d206269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21454 q = 1) (hb : d202307 q = 1) : d206280 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21454, d206280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21454, d206280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48004 (p : Pattern) (ha : d21460 p = 1) (hb : d202307 p = 1) : d206286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21445 q = 1) (hb : d202307 q = 1) : d206271 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21445, d206271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47999 q ha hb
    | true =>
      simp only [d21445, d206271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48000 q ha hb
  have h2 (q : Pattern) (ha : d21446 q = 1) (hb : d202307 q = 1) : d206272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d206272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21446, d206272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21447 q = 1) (hb : d202307 q = 1) : d206273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d206273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21447, d206273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21448 q = 1) (hb : d202307 q = 1) : d206274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d206274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21448, d206274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21449 q = 1) (hb : d202307 q = 1) : d206275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d206275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21449, d206275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21455 q = 1) (hb : d202307 q = 1) : d206281 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21455, d206281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48002 q ha hb
    | true =>
      simp only [d21455, d206281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48003 q ha hb
  have h7 (q : Pattern) (ha : d21456 q = 1) (hb : d202307 q = 1) : d206282 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21456, d206282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21456, d206282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21457 q = 1) (hb : d202307 q = 1) : d206283 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21457, d206283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21457, d206283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21458 q = 1) (hb : d202307 q = 1) : d206284 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21458, d206284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21458, d206284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21459 q = 1) (hb : d202307 q = 1) : d206285 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21459, d206285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21459, d206285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21460 q = 1) (hb : d202307 q = 1) : d206286 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21460, d206286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21460, d206286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48005 (p : Pattern) (ha : d21591 p = 1) (hb : d202307 p = 1) : d206385 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21445 q = 1) (hb : d202307 q = 1) : d206271 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21445, d206271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47999 q ha hb
    | true =>
      simp only [d21445, d206271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48000 q ha hb
  have h2 (q : Pattern) (ha : d21446 q = 1) (hb : d202307 q = 1) : d206272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d206272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21446, d206272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21447 q = 1) (hb : d202307 q = 1) : d206273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d206273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21447, d206273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21448 q = 1) (hb : d202307 q = 1) : d206274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d206274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21448, d206274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21449 q = 1) (hb : d202307 q = 1) : d206275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d206275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21449, d206275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21586 q = 1) (hb : d202307 q = 1) : d206380 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21586, d206380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48000 q ha hb
    | true =>
      simp only [d21586, d206380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21587 q = 1) (hb : d202307 q = 1) : d206381 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21587, d206381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21587, d206381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21588 q = 1) (hb : d202307 q = 1) : d206382 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21588, d206382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21588, d206382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21589 q = 1) (hb : d202307 q = 1) : d206383 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21589, d206383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21589, d206383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21590 q = 1) (hb : d202307 q = 1) : d206384 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21590, d206384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21590, d206384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21591 q = 1) (hb : d202307 q = 1) : d206385 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21591, d206385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21591, d206385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48006 (p : Pattern) (ha : d21597 p = 1) (hb : d202307 p = 1) : d206391 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21586 q = 1) (hb : d202307 q = 1) : d206380 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21586, d206380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48000 q ha hb
    | true =>
      simp only [d21586, d206380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21587 q = 1) (hb : d202307 q = 1) : d206381 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21587, d206381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21587, d206381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21588 q = 1) (hb : d202307 q = 1) : d206382 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21588, d206382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21588, d206382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21589 q = 1) (hb : d202307 q = 1) : d206383 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21589, d206383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21589, d206383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21590 q = 1) (hb : d202307 q = 1) : d206384 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21590, d206384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21590, d206384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21592 q = 1) (hb : d202307 q = 1) : d206386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21592, d206386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48003 q ha hb
    | true =>
      simp only [d21592, d206386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21593 q = 1) (hb : d202307 q = 1) : d206387 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21593, d206387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21593, d206387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21594 q = 1) (hb : d202307 q = 1) : d206388 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21594, d206388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21594, d206388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21595 q = 1) (hb : d202307 q = 1) : d206389 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21595, d206389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21595, d206389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21596 q = 1) (hb : d202307 q = 1) : d206390 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21596, d206390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21596, d206390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21597 q = 1) (hb : d202307 q = 1) : d206391 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21597, d206391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21597, d206391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48007 (p : Pattern) (ha : d21606 p = 1) (hb : d202307 p = 1) : d206400 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21592 q = 1) (hb : d202307 q = 1) : d206386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21592, d206386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48003 q ha hb
    | true =>
      simp only [d21592, d206386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21593 q = 1) (hb : d202307 q = 1) : d206387 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21593, d206387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21593, d206387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21594 q = 1) (hb : d202307 q = 1) : d206388 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21594, d206388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21594, d206388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21595 q = 1) (hb : d202307 q = 1) : d206389 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21595, d206389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21595, d206389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21596 q = 1) (hb : d202307 q = 1) : d206390 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21596, d206390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21596, d206390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21606 q = 1) (hb : d202307 q = 1) : d206400 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21606, d206400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21606, d206400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48008 (p : Pattern) (ha : d986 p = 1) (hb : d202307 p = 1) : d205941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d971 q = 1) (hb : d202307 q = 1) : d205936 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d205936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d205936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47905 q ha hb
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d202307 q = 1) : d205895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47905 q ha hb
    | true =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d972 q = 1) (hb : d202307 q = 1) : d205937 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d205937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d972, d205937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d752 q = 1) (hb : d202307 q = 1) : d205896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d973 q = 1) (hb : d202307 q = 1) : d205938 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d205938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d973, d205938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d974 q = 1) (hb : d202307 q = 1) : d205939 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d205939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d974, d205939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d980 q = 1) (hb : d202307 q = 1) : d205940 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d205940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d980, d205940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d986 q = 1) (hb : d202307 q = 1) : d205941 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d986, d205941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d986, d205941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48009 (p : Pattern) (ha : d21633 p = 1) (hb : d202307 p = 1) : d206061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21071 q = 1) (hb : d202307 q = 1) : d206056 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d206056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21071, d206056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47929 q ha hb
  have h2 (q : Pattern) (ha : d20990 q = 1) (hb : d202307 q = 1) : d206002 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d206002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47929 q ha hb
    | true =>
      simp only [d20990, d206002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21072 q = 1) (hb : d202307 q = 1) : d206057 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d206057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21072, d206057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20991 q = 1) (hb : d202307 q = 1) : d206003 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d206003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20991, d206003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21073 q = 1) (hb : d202307 q = 1) : d206058 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d206058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21073, d206058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21074 q = 1) (hb : d202307 q = 1) : d206059 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d206059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21074, d206059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d202307 q = 1) : d205936 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d205936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d205936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47905 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d202307 q = 1) : d205895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47905 q ha hb
    | true =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d202307 q = 1) : d205937 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d205937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d205937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d202307 q = 1) : d205896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d202307 q = 1) : d205938 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d205938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d205938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d202307 q = 1) : d205939 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d205939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d205939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21075 q = 1) (hb : d202307 q = 1) : d206060 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21075, d206060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21075, d206060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d980 q = 1) (hb : d202307 q = 1) : d205940 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d205940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d980, d205940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d21633 q = 1) (hb : d202307 q = 1) : d206061 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21633, d206061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21633, d206061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48010 (p : Pattern) (ha : d21655 p = 1) (hb : d202307 p = 1) : d206439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21637 q = 1) (hb : d202307 q = 1) : d206062 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21637, d206062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48009 q ha hb
    | true =>
      simp only [d21637, d206062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48008 q ha hb
  have h2 (q : Pattern) (ha : d21638 q = 1) (hb : d202307 q = 1) : d206063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21638, d206063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21638, d206063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21639 q = 1) (hb : d202307 q = 1) : d206064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21639, d206064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21639, d206064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21645 q = 1) (hb : d202307 q = 1) : d206429 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21645, d206429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21645, d206429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21654 q = 1) (hb : d202307 q = 1) : d206438 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21654, d206438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21654, d206438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21655 q = 1) (hb : d202307 q = 1) : d206439 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21655, d206439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21655, d206439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48011 (p : Pattern) (ha : d21715 p = 1) (hb : d202307 p = 1) : d206462 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21656 q = 1) (hb : d202307 q = 1) : d206440 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21656, d206440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48010 q ha hb
    | true =>
      simp only [d21656, d206440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21657 q = 1) (hb : d202307 q = 1) : d206441 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21657, d206441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21657, d206441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21712 q = 1) (hb : d202307 q = 1) : d206459 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21712, d206459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21712, d206459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21713 q = 1) (hb : d202307 q = 1) : d206460 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21713, d206460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21713, d206460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21714 q = 1) (hb : d202307 q = 1) : d206461 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21714, d206461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21714, d206461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21715 q = 1) (hb : d202307 q = 1) : d206462 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21715, d206462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21715, d206462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48012 (p : Pattern) (ha : d21721 p = 1) (hb : d202307 p = 1) : d206468 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21716 q = 1) (hb : d202307 q = 1) : d206463 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21716, d206463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48011 q ha hb
    | true =>
      simp only [d21716, d206463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21717 q = 1) (hb : d202307 q = 1) : d206464 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21717, d206464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21717, d206464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21718 q = 1) (hb : d202307 q = 1) : d206465 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21718, d206465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21718, d206465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21719 q = 1) (hb : d202307 q = 1) : d206466 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21719, d206466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21719, d206466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21720 q = 1) (hb : d202307 q = 1) : d206467 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21720, d206467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21720, d206467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21721 q = 1) (hb : d202307 q = 1) : d206468 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21721, d206468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21721, d206468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48013 (p : Pattern) (ha : d21465 p = 1) (hb : d202307 p = 1) : d206291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d202307 q = 1) : d206257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d206257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47997 q ha hb
    | true =>
      simp only [d21431, d206257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d202307 q = 1) : d206258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d206258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d206258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d202307 q = 1) : d206261 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47998 q ha hb
    | true =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d202307 q = 1) : d206262 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d202307 q = 1) : d206263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d206263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d206263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d202307 q = 1) : d206264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d206264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d206264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21464 q = 1) (hb : d202307 q = 1) : d206290 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21464, d206290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21464, d206290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21465 q = 1) (hb : d202307 q = 1) : d206291 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21465, d206291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21465, d206291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48014 (p : Pattern) (ha : d21467 p = 1) (hb : d202307 p = 1) : d206293 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d202307 q = 1) : d206261 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47998 q ha hb
    | true =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d202307 q = 1) : d206262 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d202307 q = 1) : d206267 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d206267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d206267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d202307 q = 1) : d206268 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d206268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d206268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21466 q = 1) (hb : d202307 q = 1) : d206292 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21466, d206292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21466, d206292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21467 q = 1) (hb : d202307 q = 1) : d206293 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21467, d206293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21467, d206293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48015 (p : Pattern) (ha : d21474 p = 1) (hb : d202307 p = 1) : d206300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d202307 q = 1) : d206257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d206257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47997 q ha hb
    | true =>
      simp only [d21431, d206257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d202307 q = 1) : d206258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d206258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d206258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d202307 q = 1) : d206261 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47998 q ha hb
    | true =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d202307 q = 1) : d206262 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d202307 q = 1) : d206263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d206263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d206263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21472 q = 1) (hb : d202307 q = 1) : d206298 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21472, d206298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21472, d206298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21473 q = 1) (hb : d202307 q = 1) : d206299 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21473, d206299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21473, d206299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21474 q = 1) (hb : d202307 q = 1) : d206300 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21474, d206300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21474, d206300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48016 (p : Pattern) (ha : d21477 p = 1) (hb : d202307 p = 1) : d206303 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d202307 q = 1) : d206261 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47998 q ha hb
    | true =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d202307 q = 1) : d206262 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d202307 q = 1) : d206267 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d206267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d206267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21475 q = 1) (hb : d202307 q = 1) : d206301 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21475, d206301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21475, d206301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21476 q = 1) (hb : d202307 q = 1) : d206302 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21476, d206302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21476, d206302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21477 q = 1) (hb : d202307 q = 1) : d206303 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21477, d206303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21477, d206303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48017 (p : Pattern) (ha : d530 p = 1) (hb : d202304 p = 1) : d30966 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d529 q = 1) : d529 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d311 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d530 q = 1) (hb : d202304 q = 1) : d30966 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d530, d202304, d30966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d530, d202304, d30966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48018 (p : Pattern) (ha : d536 p = 1) (hb : d202304 p = 1) : d30970 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d535 q = 1) : d535 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d536 q = 1) (hb : d202304 q = 1) : d30970 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d536, d202304, d30970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d536, d202304, d30970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48019 (p : Pattern) (ha : d21481 p = 1) (hb : d202307 p = 1) : d206311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d823 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d531 q = 1) (hb : d202304 q = 1) : d30967 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48017 q ha hb
    | true =>
      simp only [d531, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d532 q = 1) (hb : d202304 q = 1) : d30968 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d532, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d824 q = 1) (hb : d202306 q = 1) : d206307 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d824, d202306, d206307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d824, d202306, d206307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d829 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d537 q = 1) (hb : d202304 q = 1) : d30971 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d30971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48018 q ha hb
    | true =>
      simp only [d537, d30971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d538 q = 1) (hb : d202304 q = 1) : d30972 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d30972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d538, d30972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d830 q = 1) (hb : d202306 q = 1) : d206308 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d830, d202306, d206308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d830, d202306, d206308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d831 q = 1) (hb : d202306 q = 1) : d206309 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d831, d206309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d831, d206309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d832 q = 1) (hb : d202306 q = 1) : d206310 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d832, d206310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d832, d206310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21481 q = 1) (hb : d202307 q = 1) : d206311 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21481, d202307, d206311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21481, d202307, d206311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro48020 (p : Pattern) (ha : d9580 p = 1) (hb : d202304 p = 1) : d206317 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d5121 q = 1) : d5121 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9579 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9580 q = 1) (hb : d202304 q = 1) : d206317 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d9580, d202304, d206317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9580, d202304, d206317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48021 (p : Pattern) (ha : d21487 p = 1) (hb : d202307 p = 1) : d206323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d532 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9581 q = 1) (hb : d202304 q = 1) : d206318 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9581, d206318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48020 q ha hb
    | true =>
      simp only [d9581, d206318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9582 q = 1) (hb : d202304 q = 1) : d206319 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d206319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9582, d206319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d9593 q = 1) (hb : d202306 q = 1) : d206320 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9593, d202306, d206320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9593, d202306, d206320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9594 q = 1) (hb : d202306 q = 1) : d206321 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9594, d206321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9594, d206321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9595 q = 1) (hb : d202306 q = 1) : d206322 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9595, d206322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9595, d206322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d21487 q = 1) (hb : d202307 q = 1) : d206323 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21487, d202307, d206323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21487, d202307, d206323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro48022 (p : Pattern) (ha : d21493 p = 1) (hb : d202307 p = 1) : d206329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21482 q = 1) (hb : d202307 q = 1) : d206312 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21482, d206312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48019 q ha hb
    | true =>
      simp only [d21482, d206312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21483 q = 1) (hb : d202307 q = 1) : d206313 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21483, d206313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21483, d206313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21484 q = 1) (hb : d202307 q = 1) : d206314 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21484, d206314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21484, d206314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21485 q = 1) (hb : d202307 q = 1) : d206315 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21485, d206315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21485, d206315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21183 q = 1) (hb : d202307 q = 1) : d206123 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d206123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47967 q ha hb
    | true =>
      simp only [d21183, d206123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21184 q = 1) (hb : d202307 q = 1) : d206124 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d206124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21184, d206124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21185 q = 1) (hb : d202307 q = 1) : d206125 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21185, d206125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21185, d206125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21186 q = 1) (hb : d202307 q = 1) : d206126 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21186, d206126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21186, d206126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21486 q = 1) (hb : d202307 q = 1) : d206316 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21486, d206316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21486, d206316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21488 q = 1) (hb : d202307 q = 1) : d206324 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21488, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48021 q ha hb
    | true =>
      simp only [d21488, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21489 q = 1) (hb : d202307 q = 1) : d206325 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21489, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21489, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21490 q = 1) (hb : d202307 q = 1) : d206326 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21490, d206326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21490, d206326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21491 q = 1) (hb : d202307 q = 1) : d206327 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21491, d206327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21491, d206327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d21189 q = 1) (hb : d202307 q = 1) : d206135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47969 q ha hb
    | true =>
      simp only [d21189, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d21190 q = 1) (hb : d202307 q = 1) : d206136 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d21190, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d21191 q = 1) (hb : d202307 q = 1) : d206137 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21191, d206137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21191, d206137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21192 q = 1) (hb : d202307 q = 1) : d206138 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21192, d206138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21192, d206138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21492 q = 1) (hb : d202307 q = 1) : d206328 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21492, d206328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21492, d206328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21493 q = 1) (hb : d202307 q = 1) : d206329 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21493, d206329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21493, d206329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro48023 (p : Pattern) (ha : d21497 p = 1) (hb : d202307 p = 1) : d206333 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21189 q = 1) (hb : d202307 q = 1) : d206135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47969 q ha hb
    | true =>
      simp only [d21189, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21190 q = 1) (hb : d202307 q = 1) : d206136 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21190, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21191 q = 1) (hb : d202307 q = 1) : d206137 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21191, d206137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21191, d206137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21192 q = 1) (hb : d202307 q = 1) : d206138 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21192, d206138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21192, d206138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d202307 q = 1) : d205895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47905 q ha hb
    | true =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d202307 q = 1) : d205896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d202307 q = 1) : d205897 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d205897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d205897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d202307 q = 1) : d205898 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d205898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d205898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21418 q = 1) (hb : d202307 q = 1) : d206139 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21418, d206139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21418, d206139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d757 q = 1) (hb : d202307 q = 1) : d205899 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d205899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d757, d205899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21497 q = 1) (hb : d202307 q = 1) : d206333 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21497, d206333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21497, d206333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48024 (p : Pattern) (ha : d21503 p = 1) (hb : d202307 p = 1) : d206339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21494 q = 1) (hb : d202307 q = 1) : d206330 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21494, d206330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48022 q ha hb
    | true =>
      simp only [d21494, d206330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47995 q ha hb
  have h2 (q : Pattern) (ha : d21495 q = 1) (hb : d202307 q = 1) : d206331 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21495, d206331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21495, d206331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21496 q = 1) (hb : d202307 q = 1) : d206332 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21496, d206332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21496, d206332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21498 q = 1) (hb : d202307 q = 1) : d206334 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21498, d206334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47995 q ha hb
    | true =>
      simp only [d21498, d206334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48023 q ha hb
  have h5 (q : Pattern) (ha : d21499 q = 1) (hb : d202307 q = 1) : d206335 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21499, d206335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21499, d206335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21500 q = 1) (hb : d202307 q = 1) : d206336 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21500, d206336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21500, d206336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21501 q = 1) (hb : d202307 q = 1) : d206337 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21501, d206337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21501, d206337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21421 q = 1) (hb : d202307 q = 1) : d206141 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21421, d206141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47995 q ha hb
    | true =>
      simp only [d21421, d206141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47996 q ha hb
  have h9 (q : Pattern) (ha : d21422 q = 1) (hb : d202307 q = 1) : d206142 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21422, d206142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21422, d206142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21423 q = 1) (hb : d202307 q = 1) : d206143 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21423, d206143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21423, d206143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21424 q = 1) (hb : d202307 q = 1) : d206008 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21424, d206008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47996 q ha hb
    | true =>
      simp only [d21424, d206008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47994 q ha hb
  have h12 (q : Pattern) (ha : d21425 q = 1) (hb : d202307 q = 1) : d206009 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21425, d206009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21425, d206009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21426 q = 1) (hb : d202307 q = 1) : d206010 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21426, d206010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21426, d206010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21427 q = 1) (hb : d202307 q = 1) : d206144 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21427, d206144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21427, d206144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21502 q = 1) (hb : d202307 q = 1) : d206338 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21502, d206338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21502, d206338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21503 q = 1) (hb : d202307 q = 1) : d206339 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21503, d206339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d21503, d206339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro48025 (p : Pattern) (ha : d21509 p = 1) (hb : d202307 p = 1) : d206345 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21504 q = 1) (hb : d202307 q = 1) : d206340 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21504, d206340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48024 q ha hb
    | true =>
      simp only [d21504, d206340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21505 q = 1) (hb : d202307 q = 1) : d206341 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21505, d206341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21505, d206341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21431 q = 1) (hb : d202307 q = 1) : d206257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d206257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47997 q ha hb
    | true =>
      simp only [d21431, d206257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21432 q = 1) (hb : d202307 q = 1) : d206258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d206258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d206258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21506 q = 1) (hb : d202307 q = 1) : d206342 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21506, d206342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21506, d206342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21507 q = 1) (hb : d202307 q = 1) : d206343 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21507, d206343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21507, d206343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21508 q = 1) (hb : d202307 q = 1) : d206344 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21508, d206344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21508, d206344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21509 q = 1) (hb : d202307 q = 1) : d206345 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21509, d206345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21509, d206345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48026 (p : Pattern) (ha : d21554 p = 1) (hb : d202307 p = 1) : d206351 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d202307 q = 1) : d206257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d206257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47997 q ha hb
    | true =>
      simp only [d21431, d206257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d202307 q = 1) : d206258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d206258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d206258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21551 q = 1) (hb : d202307 q = 1) : d206348 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21551, d206348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21551, d206348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21552 q = 1) (hb : d202307 q = 1) : d206349 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21552, d206349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21552, d206349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21553 q = 1) (hb : d202307 q = 1) : d206350 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21553, d206350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21553, d206350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21554 q = 1) (hb : d202307 q = 1) : d206351 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21554, d206351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21554, d206351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48027 (p : Pattern) (ha : d150118 p = 1) (hb : d202307 p = 1) : d206357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21468 q = 1) (hb : d202307 q = 1) : d206294 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21468, d206294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48013 q ha hb
    | true =>
      simp only [d21468, d206294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48014 q ha hb
  have h2 (q : Pattern) (ha : d21469 q = 1) (hb : d202307 q = 1) : d206295 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21469, d206295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21469, d206295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21470 q = 1) (hb : d202307 q = 1) : d206296 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21470, d206296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21470, d206296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21471 q = 1) (hb : d202307 q = 1) : d206297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21471, d206297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21471, d206297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21478 q = 1) (hb : d202307 q = 1) : d206304 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21478, d206304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48015 q ha hb
    | true =>
      simp only [d21478, d206304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48016 q ha hb
  have h6 (q : Pattern) (ha : d21479 q = 1) (hb : d202307 q = 1) : d206305 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21479, d206305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21479, d206305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21480 q = 1) (hb : d202307 q = 1) : d206306 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21480, d206306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21480, d206306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21510 q = 1) (hb : d202307 q = 1) : d206346 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21510, d206346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48025 q ha hb
    | true =>
      simp only [d21510, d206346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47999 q ha hb
  have h9 (q : Pattern) (ha : d150114 q = 1) (hb : d202307 q = 1) : d206347 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150114, d206347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150114, d206347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21555 q = 1) (hb : d202307 q = 1) : d206352 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21555, d206352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48026 q ha hb
    | true =>
      simp only [d21555, d206352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21556 q = 1) (hb : d202307 q = 1) : d206353 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21556, d206353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21556, d206353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150115 q = 1) (hb : d202307 q = 1) : d206354 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150115, d206354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150115, d206354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150116 q = 1) (hb : d202307 q = 1) : d206355 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150116, d206355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150116, d206355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150117 q = 1) (hb : d202307 q = 1) : d206356 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150117, d206356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150117, d206356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150118 q = 1) (hb : d202307 q = 1) : d206357 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150118, d206357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150118, d206357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48028 (p : Pattern) (ha : d21561 p = 1) (hb : d202307 p = 1) : d206358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d202307 q = 1) : d206257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d206257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47997 q ha hb
    | true =>
      simp only [d21431, d206257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d202307 q = 1) : d206258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d206258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d206258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d202307 q = 1) : d206261 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47998 q ha hb
    | true =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d202307 q = 1) : d206262 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d202307 q = 1) : d206263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d206263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d206263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d202307 q = 1) : d206264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d206264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d206264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21464 q = 1) (hb : d202307 q = 1) : d206290 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21464, d206290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21464, d206290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21561 q = 1) (hb : d202307 q = 1) : d206358 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21561, d206358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21561, d206358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48029 (p : Pattern) (ha : d21562 p = 1) (hb : d202307 p = 1) : d206359 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d202307 q = 1) : d206261 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47998 q ha hb
    | true =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d202307 q = 1) : d206262 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d202307 q = 1) : d206267 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d206267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d206267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d202307 q = 1) : d206268 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d206268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d206268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21466 q = 1) (hb : d202307 q = 1) : d206292 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21466, d206292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21466, d206292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21562 q = 1) (hb : d202307 q = 1) : d206359 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21562, d206359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21562, d206359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48030 (p : Pattern) (ha : d21567 p = 1) (hb : d202307 p = 1) : d206364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d202307 q = 1) : d206257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d206257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47997 q ha hb
    | true =>
      simp only [d21431, d206257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d202307 q = 1) : d206258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d206258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d206258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d202307 q = 1) : d206261 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47998 q ha hb
    | true =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d202307 q = 1) : d206262 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d202307 q = 1) : d206263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d206263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d206263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21472 q = 1) (hb : d202307 q = 1) : d206298 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21472, d206298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21472, d206298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21473 q = 1) (hb : d202307 q = 1) : d206299 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21473, d206299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21473, d206299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21567 q = 1) (hb : d202307 q = 1) : d206364 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21567, d206364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21567, d206364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48031 (p : Pattern) (ha : d21568 p = 1) (hb : d202307 p = 1) : d206365 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d202307 q = 1) : d206261 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47998 q ha hb
    | true =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d202307 q = 1) : d206262 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d202307 q = 1) : d206267 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d206267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d206267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21475 q = 1) (hb : d202307 q = 1) : d206301 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21475, d206301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21475, d206301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21476 q = 1) (hb : d202307 q = 1) : d206302 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21476, d206302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21476, d206302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21568 q = 1) (hb : d202307 q = 1) : d206365 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21568, d206365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21568, d206365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48032 (p : Pattern) (ha : d21572 p = 1) (hb : d202307 p = 1) : d206369 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21504 q = 1) (hb : d202307 q = 1) : d206340 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21504, d206340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48024 q ha hb
    | true =>
      simp only [d21504, d206340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21505 q = 1) (hb : d202307 q = 1) : d206341 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21505, d206341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21505, d206341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21431 q = 1) (hb : d202307 q = 1) : d206257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d206257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47997 q ha hb
    | true =>
      simp only [d21431, d206257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21432 q = 1) (hb : d202307 q = 1) : d206258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d206258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d206258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21506 q = 1) (hb : d202307 q = 1) : d206342 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21506, d206342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21506, d206342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21507 q = 1) (hb : d202307 q = 1) : d206343 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21507, d206343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21507, d206343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21508 q = 1) (hb : d202307 q = 1) : d206344 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21508, d206344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21508, d206344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21572 q = 1) (hb : d202307 q = 1) : d206369 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21572, d206369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21572, d206369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48033 (p : Pattern) (ha : d21578 p = 1) (hb : d202307 p = 1) : d206372 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d202307 q = 1) : d206257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d206257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47997 q ha hb
    | true =>
      simp only [d21431, d206257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d202307 q = 1) : d206258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d206258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d206258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21551 q = 1) (hb : d202307 q = 1) : d206348 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21551, d206348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21551, d206348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21552 q = 1) (hb : d202307 q = 1) : d206349 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21552, d206349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21552, d206349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21553 q = 1) (hb : d202307 q = 1) : d206350 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21553, d206350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21553, d206350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21578 q = 1) (hb : d202307 q = 1) : d206372 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21578, d206372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21578, d206372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48034 (p : Pattern) (ha : d150123 p = 1) (hb : d202307 p = 1) : d206378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21468 q = 1) (hb : d202307 q = 1) : d206294 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21468, d206294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48013 q ha hb
    | true =>
      simp only [d21468, d206294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48014 q ha hb
  have h2 (q : Pattern) (ha : d21469 q = 1) (hb : d202307 q = 1) : d206295 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21469, d206295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21469, d206295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21470 q = 1) (hb : d202307 q = 1) : d206296 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21470, d206296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21470, d206296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21471 q = 1) (hb : d202307 q = 1) : d206297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21471, d206297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21471, d206297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21478 q = 1) (hb : d202307 q = 1) : d206304 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21478, d206304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48015 q ha hb
    | true =>
      simp only [d21478, d206304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48016 q ha hb
  have h6 (q : Pattern) (ha : d21479 q = 1) (hb : d202307 q = 1) : d206305 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21479, d206305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21479, d206305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21480 q = 1) (hb : d202307 q = 1) : d206306 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21480, d206306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21480, d206306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21510 q = 1) (hb : d202307 q = 1) : d206346 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21510, d206346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48025 q ha hb
    | true =>
      simp only [d21510, d206346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47999 q ha hb
  have h9 (q : Pattern) (ha : d150114 q = 1) (hb : d202307 q = 1) : d206347 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150114, d206347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150114, d206347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21555 q = 1) (hb : d202307 q = 1) : d206352 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21555, d206352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48026 q ha hb
    | true =>
      simp only [d21555, d206352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21556 q = 1) (hb : d202307 q = 1) : d206353 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21556, d206353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21556, d206353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150115 q = 1) (hb : d202307 q = 1) : d206354 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150115, d206354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150115, d206354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150116 q = 1) (hb : d202307 q = 1) : d206355 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150116, d206355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150116, d206355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150117 q = 1) (hb : d202307 q = 1) : d206356 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150117, d206356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150117, d206356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21563 q = 1) (hb : d202307 q = 1) : d206360 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21563, d206360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48028 q ha hb
    | true =>
      simp only [d21563, d206360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48029 q ha hb
  have h16 (q : Pattern) (ha : d21564 q = 1) (hb : d202307 q = 1) : d206361 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21564, d206361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21564, d206361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21565 q = 1) (hb : d202307 q = 1) : d206362 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21565, d206362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21565, d206362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21566 q = 1) (hb : d202307 q = 1) : d206363 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21566, d206363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21566, d206363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21569 q = 1) (hb : d202307 q = 1) : d206366 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21569, d206366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48030 q ha hb
    | true =>
      simp only [d21569, d206366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48031 q ha hb
  have h20 (q : Pattern) (ha : d21570 q = 1) (hb : d202307 q = 1) : d206367 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21570, d206367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21570, d206367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d21571 q = 1) (hb : d202307 q = 1) : d206368 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21571, d206368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d21571, d206368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d21573 q = 1) (hb : d202307 q = 1) : d206370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21573, d206370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48032 q ha hb
    | true =>
      simp only [d21573, d206370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48002 q ha hb
  have h23 (q : Pattern) (ha : d150119 q = 1) (hb : d202307 q = 1) : d206371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150119, d206371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d150119, d206371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d21579 q = 1) (hb : d202307 q = 1) : d206373 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21579, d206373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48033 q ha hb
    | true =>
      simp only [d21579, d206373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d21580 q = 1) (hb : d202307 q = 1) : d206374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21580, d206374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21580, d206374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d150120 q = 1) (hb : d202307 q = 1) : d206375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150120, d206375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150120, d206375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d150121 q = 1) (hb : d202307 q = 1) : d206376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150121, d206376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150121, d206376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d150122 q = 1) (hb : d202307 q = 1) : d206377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150122, d206377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d150122, d206377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d150123 q = 1) (hb : d202307 q = 1) : d206378 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150123, d206378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150123, d206378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro48035 (p : Pattern) (ha : d150130 p = 1) (hb : d202307 p = 1) : d206398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21573 q = 1) (hb : d202307 q = 1) : d206370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21573, d206370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48032 q ha hb
    | true =>
      simp only [d21573, d206370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48002 q ha hb
  have h2 (q : Pattern) (ha : d150119 q = 1) (hb : d202307 q = 1) : d206371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150119, d206371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150119, d206371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21579 q = 1) (hb : d202307 q = 1) : d206373 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21579, d206373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48033 q ha hb
    | true =>
      simp only [d21579, d206373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21580 q = 1) (hb : d202307 q = 1) : d206374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21580, d206374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21580, d206374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150120 q = 1) (hb : d202307 q = 1) : d206375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150120, d206375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150120, d206375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150128 q = 1) (hb : d202307 q = 1) : d206396 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150128, d206396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150128, d206396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150129 q = 1) (hb : d202307 q = 1) : d206397 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150129, d206397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150129, d206397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150130 q = 1) (hb : d202307 q = 1) : d206398 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150130, d206398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150130, d206398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48036 (p : Pattern) (ha : d21622 p = 1) (hb : d202307 p = 1) : d206416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21612 q = 1) (hb : d202307 q = 1) : d206406 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21612, d206406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21612, d206406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48019 q ha hb
  have h2 (q : Pattern) (ha : d21482 q = 1) (hb : d202307 q = 1) : d206312 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21482, d206312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48019 q ha hb
    | true =>
      simp only [d21482, d206312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21613 q = 1) (hb : d202307 q = 1) : d206407 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21613, d206407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21613, d206407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21483 q = 1) (hb : d202307 q = 1) : d206313 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21483, d206313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21483, d206313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21614 q = 1) (hb : d202307 q = 1) : d206408 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21614, d206408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21614, d206408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21615 q = 1) (hb : d202307 q = 1) : d206409 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21615, d206409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21615, d206409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21309 q = 1) (hb : d202307 q = 1) : d206200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21309, d206200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21309, d206200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47967 q ha hb
  have h8 (q : Pattern) (ha : d21183 q = 1) (hb : d202307 q = 1) : d206123 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d206123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47967 q ha hb
    | true =>
      simp only [d21183, d206123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21310 q = 1) (hb : d202307 q = 1) : d206201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21310, d206201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21310, d206201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21184 q = 1) (hb : d202307 q = 1) : d206124 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d206124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21184, d206124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21311 q = 1) (hb : d202307 q = 1) : d206202 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21311, d206202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21311, d206202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21312 q = 1) (hb : d202307 q = 1) : d206203 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21312, d206203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21312, d206203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21616 q = 1) (hb : d202307 q = 1) : d206410 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21616, d206410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21616, d206410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21617 q = 1) (hb : d202307 q = 1) : d206411 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21617, d206411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21617, d206411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48021 q ha hb
  have h15 (q : Pattern) (ha : d21488 q = 1) (hb : d202307 q = 1) : d206324 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21488, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48021 q ha hb
    | true =>
      simp only [d21488, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d21618 q = 1) (hb : d202307 q = 1) : d206412 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21618, d206412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d21618, d206412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21489 q = 1) (hb : d202307 q = 1) : d206325 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21489, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d21489, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21619 q = 1) (hb : d202307 q = 1) : d206413 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21619, d206413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21619, d206413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21620 q = 1) (hb : d202307 q = 1) : d206414 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21620, d206414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d21620, d206414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d21314 q = 1) (hb : d202307 q = 1) : d206205 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21314, d206205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21314, d206205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47969 q ha hb
  have h21 (q : Pattern) (ha : d21189 q = 1) (hb : d202307 q = 1) : d206135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47969 q ha hb
    | true =>
      simp only [d21189, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d21315 q = 1) (hb : d202307 q = 1) : d206206 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21315, d206206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d21315, d206206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d21190 q = 1) (hb : d202307 q = 1) : d206136 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d21190, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d21316 q = 1) (hb : d202307 q = 1) : d206207 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21316, d206207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d21316, d206207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d21317 q = 1) (hb : d202307 q = 1) : d206208 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21317, d206208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21317, d206208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d21621 q = 1) (hb : d202307 q = 1) : d206415 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21621, d206415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d21621, d206415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d21622 q = 1) (hb : d202307 q = 1) : d206416 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21622, d206416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21622, d206416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro48037 (p : Pattern) (ha : d21624 p = 1) (hb : d202307 p = 1) : d206210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21309 q = 1) (hb : d202307 q = 1) : d206200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21309, d206200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21309, d206200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47967 q ha hb
  have h2 (q : Pattern) (ha : d21183 q = 1) (hb : d202307 q = 1) : d206123 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d206123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47967 q ha hb
    | true =>
      simp only [d21183, d206123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21310 q = 1) (hb : d202307 q = 1) : d206201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21310, d206201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21310, d206201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21184 q = 1) (hb : d202307 q = 1) : d206124 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d206124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21184, d206124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21311 q = 1) (hb : d202307 q = 1) : d206202 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21311, d206202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21311, d206202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21312 q = 1) (hb : d202307 q = 1) : d206203 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21312, d206203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21312, d206203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21071 q = 1) (hb : d202307 q = 1) : d206056 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d206056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21071, d206056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47929 q ha hb
  have h8 (q : Pattern) (ha : d20990 q = 1) (hb : d202307 q = 1) : d206002 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d206002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47929 q ha hb
    | true =>
      simp only [d20990, d206002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21072 q = 1) (hb : d202307 q = 1) : d206057 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d206057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21072, d206057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20991 q = 1) (hb : d202307 q = 1) : d206003 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d206003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20991, d206003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21073 q = 1) (hb : d202307 q = 1) : d206058 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d206058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21073, d206058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21074 q = 1) (hb : d202307 q = 1) : d206059 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d206059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21074, d206059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21313 q = 1) (hb : d202307 q = 1) : d206204 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21313, d206204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21313, d206204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21314 q = 1) (hb : d202307 q = 1) : d206205 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21314, d206205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21314, d206205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47969 q ha hb
  have h15 (q : Pattern) (ha : d21189 q = 1) (hb : d202307 q = 1) : d206135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47969 q ha hb
    | true =>
      simp only [d21189, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d21315 q = 1) (hb : d202307 q = 1) : d206206 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21315, d206206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d21315, d206206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21190 q = 1) (hb : d202307 q = 1) : d206136 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d21190, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21316 q = 1) (hb : d202307 q = 1) : d206207 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21316, d206207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21316, d206207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21317 q = 1) (hb : d202307 q = 1) : d206208 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21317, d206208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d21317, d206208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d971 q = 1) (hb : d202307 q = 1) : d205936 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d205936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d205936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47905 q ha hb
  have h21 (q : Pattern) (ha : d751 q = 1) (hb : d202307 q = 1) : d205895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47905 q ha hb
    | true =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d972 q = 1) (hb : d202307 q = 1) : d205937 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d205937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d972, d205937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d752 q = 1) (hb : d202307 q = 1) : d205896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d973 q = 1) (hb : d202307 q = 1) : d205938 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d205938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d973, d205938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d974 q = 1) (hb : d202307 q = 1) : d205939 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d205939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d974, d205939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d21623 q = 1) (hb : d202307 q = 1) : d206209 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21623, d206209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d21623, d206209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d21624 q = 1) (hb : d202307 q = 1) : d206210 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21624, d206210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21624, d206210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro48038 (p : Pattern) (ha : d21628 p = 1) (hb : d202307 p = 1) : d206420 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21314 q = 1) (hb : d202307 q = 1) : d206205 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21314, d206205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21314, d206205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47969 q ha hb
  have h2 (q : Pattern) (ha : d21189 q = 1) (hb : d202307 q = 1) : d206135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47969 q ha hb
    | true =>
      simp only [d21189, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21315 q = 1) (hb : d202307 q = 1) : d206206 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21315, d206206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21315, d206206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21190 q = 1) (hb : d202307 q = 1) : d206136 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21190, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21316 q = 1) (hb : d202307 q = 1) : d206207 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21316, d206207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21316, d206207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21317 q = 1) (hb : d202307 q = 1) : d206208 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21317, d206208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21317, d206208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d202307 q = 1) : d205936 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d205936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d205936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47905 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d202307 q = 1) : d205895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47905 q ha hb
    | true =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d202307 q = 1) : d205937 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d205937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d205937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d202307 q = 1) : d205896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d202307 q = 1) : d205938 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d205938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d205938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d202307 q = 1) : d205939 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d205939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d205939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21623 q = 1) (hb : d202307 q = 1) : d206209 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21623, d206209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21623, d206209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d980 q = 1) (hb : d202307 q = 1) : d205940 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d205940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d980, d205940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d21628 q = 1) (hb : d202307 q = 1) : d206420 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21628, d206420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21628, d206420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48039 (p : Pattern) (ha : d21642 p = 1) (hb : d202307 p = 1) : d206426 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21625 q = 1) (hb : d202307 q = 1) : d206417 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21625, d206417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48036 q ha hb
    | true =>
      simp only [d21625, d206417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48037 q ha hb
  have h2 (q : Pattern) (ha : d21626 q = 1) (hb : d202307 q = 1) : d206418 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21626, d206418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21626, d206418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21627 q = 1) (hb : d202307 q = 1) : d206419 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21627, d206419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21627, d206419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21629 q = 1) (hb : d202307 q = 1) : d206421 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21629, d206421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48037 q ha hb
    | true =>
      simp only [d21629, d206421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48038 q ha hb
  have h5 (q : Pattern) (ha : d21630 q = 1) (hb : d202307 q = 1) : d206422 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21630, d206422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21630, d206422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21631 q = 1) (hb : d202307 q = 1) : d206423 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21631, d206423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21631, d206423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21632 q = 1) (hb : d202307 q = 1) : d206424 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21632, d206424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21632, d206424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21634 q = 1) (hb : d202307 q = 1) : d206211 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21634, d206211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48037 q ha hb
    | true =>
      simp only [d21634, d206211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48009 q ha hb
  have h9 (q : Pattern) (ha : d21635 q = 1) (hb : d202307 q = 1) : d206212 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21635, d206212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21635, d206212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21636 q = 1) (hb : d202307 q = 1) : d206213 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21636, d206213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21636, d206213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21637 q = 1) (hb : d202307 q = 1) : d206062 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21637, d206062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48009 q ha hb
    | true =>
      simp only [d21637, d206062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48008 q ha hb
  have h12 (q : Pattern) (ha : d21638 q = 1) (hb : d202307 q = 1) : d206063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21638, d206063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21638, d206063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21639 q = 1) (hb : d202307 q = 1) : d206064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21639, d206064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21639, d206064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21640 q = 1) (hb : d202307 q = 1) : d206214 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21640, d206214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21640, d206214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21641 q = 1) (hb : d202307 q = 1) : d206425 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21641, d206425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21641, d206425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21642 q = 1) (hb : d202307 q = 1) : d206426 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21642, d206426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d21642, d206426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro48040 (p : Pattern) (ha : d21647 p = 1) (hb : d202307 p = 1) : d206431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21634 q = 1) (hb : d202307 q = 1) : d206211 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21634, d206211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48037 q ha hb
    | true =>
      simp only [d21634, d206211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48009 q ha hb
  have h2 (q : Pattern) (ha : d21635 q = 1) (hb : d202307 q = 1) : d206212 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21635, d206212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21635, d206212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21636 q = 1) (hb : d202307 q = 1) : d206213 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21636, d206213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21636, d206213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21637 q = 1) (hb : d202307 q = 1) : d206062 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21637, d206062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48009 q ha hb
    | true =>
      simp only [d21637, d206062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48008 q ha hb
  have h5 (q : Pattern) (ha : d21638 q = 1) (hb : d202307 q = 1) : d206063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21638, d206063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21638, d206063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21639 q = 1) (hb : d202307 q = 1) : d206064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21639, d206064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21639, d206064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21640 q = 1) (hb : d202307 q = 1) : d206214 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21640, d206214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21640, d206214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21645 q = 1) (hb : d202307 q = 1) : d206429 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21645, d206429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21645, d206429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21646 q = 1) (hb : d202307 q = 1) : d206430 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21646, d206430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21646, d206430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21647 q = 1) (hb : d202307 q = 1) : d206431 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21647, d206431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21647, d206431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro48041 (p : Pattern) (ha : d21653 p = 1) (hb : d202307 p = 1) : d206437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21643 q = 1) (hb : d202307 q = 1) : d206427 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21643, d206427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48039 q ha hb
    | true =>
      simp only [d21643, d206427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21644 q = 1) (hb : d202307 q = 1) : d206428 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21644, d206428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21644, d206428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21648 q = 1) (hb : d202307 q = 1) : d206432 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21648, d206432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48040 q ha hb
    | true =>
      simp only [d21648, d206432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21649 q = 1) (hb : d202307 q = 1) : d206433 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21649, d206433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21649, d206433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21650 q = 1) (hb : d202307 q = 1) : d206434 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21650, d206434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21650, d206434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21651 q = 1) (hb : d202307 q = 1) : d206435 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21651, d206435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21651, d206435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21652 q = 1) (hb : d202307 q = 1) : d206436 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21652, d206436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21652, d206436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21653 q = 1) (hb : d202307 q = 1) : d206437 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21653, d206437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21653, d206437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48042 (p : Pattern) (ha : d21661 p = 1) (hb : d202307 p = 1) : d206445 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21648 q = 1) (hb : d202307 q = 1) : d206432 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21648, d206432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48040 q ha hb
    | true =>
      simp only [d21648, d206432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21649 q = 1) (hb : d202307 q = 1) : d206433 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21649, d206433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21649, d206433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21656 q = 1) (hb : d202307 q = 1) : d206440 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21656, d206440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48010 q ha hb
    | true =>
      simp only [d21656, d206440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21657 q = 1) (hb : d202307 q = 1) : d206441 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21657, d206441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21657, d206441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21658 q = 1) (hb : d202307 q = 1) : d206442 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21658, d206442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21658, d206442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21659 q = 1) (hb : d202307 q = 1) : d206443 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21659, d206443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21659, d206443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21660 q = 1) (hb : d202307 q = 1) : d206444 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21660, d206444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21660, d206444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21661 q = 1) (hb : d202307 q = 1) : d206445 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21661, d206445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21661, d206445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48043 (p : Pattern) (ha : d21704 p = 1) (hb : d202307 p = 1) : d206451 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21648 q = 1) (hb : d202307 q = 1) : d206432 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21648, d206432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48040 q ha hb
    | true =>
      simp only [d21648, d206432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21649 q = 1) (hb : d202307 q = 1) : d206433 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21649, d206433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21649, d206433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21701 q = 1) (hb : d202307 q = 1) : d206448 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21701, d206448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21701, d206448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21702 q = 1) (hb : d202307 q = 1) : d206449 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21702, d206449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21702, d206449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21703 q = 1) (hb : d202307 q = 1) : d206450 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21703, d206450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21703, d206450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21704 q = 1) (hb : d202307 q = 1) : d206451 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21704, d206451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21704, d206451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48044 (p : Pattern) (ha : d150140 p = 1) (hb : d202307 p = 1) : d206457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21662 q = 1) (hb : d202307 q = 1) : d206446 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21662, d206446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48041 q ha hb
    | true =>
      simp only [d21662, d206446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48042 q ha hb
  have h2 (q : Pattern) (ha : d150136 q = 1) (hb : d202307 q = 1) : d206447 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150136, d206447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150136, d206447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21705 q = 1) (hb : d202307 q = 1) : d206452 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21705, d206452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48043 q ha hb
    | true =>
      simp only [d21705, d206452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21706 q = 1) (hb : d202307 q = 1) : d206453 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21706, d206453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21706, d206453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150137 q = 1) (hb : d202307 q = 1) : d206454 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150137, d206454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150137, d206454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150138 q = 1) (hb : d202307 q = 1) : d206455 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150138, d206455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150138, d206455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150139 q = 1) (hb : d202307 q = 1) : d206456 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150139, d206456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150139, d206456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150140 q = 1) (hb : d202307 q = 1) : d206457 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150140, d206457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150140, d206457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48045 (p : Pattern) (ha : d150146 p = 1) (hb : d202307 p = 1) : d206474 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21451 q = 1) (hb : d202307 q = 1) : d206277 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21451, d206277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21451, d206277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48001 q ha hb
  have h2 (q : Pattern) (ha : d21452 q = 1) (hb : d202307 q = 1) : d206278 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21452, d206278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21452, d206278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21461 q = 1) (hb : d202307 q = 1) : d206287 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21461, d206287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48001 q ha hb
    | true =>
      simp only [d21461, d206287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48004 q ha hb
  have h4 (q : Pattern) (ha : d21462 q = 1) (hb : d202307 q = 1) : d206288 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21462, d206288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21462, d206288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21463 q = 1) (hb : d202307 q = 1) : d206289 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d21463, d206289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21463, d206289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150124 q = 1) (hb : d202307 q = 1) : d206379 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150124, d206379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48027 q ha hb
    | true =>
      simp only [d150124, d206379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48034 q ha hb
  have h7 (q : Pattern) (ha : d21598 q = 1) (hb : d202307 q = 1) : d206392 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21598, d206392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48005 q ha hb
    | true =>
      simp only [d21598, d206392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48006 q ha hb
  have h8 (q : Pattern) (ha : d150125 q = 1) (hb : d202307 q = 1) : d206393 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150125, d206393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150125, d206393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150126 q = 1) (hb : d202307 q = 1) : d206394 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150126, d206394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150126, d206394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d150127 q = 1) (hb : d202307 q = 1) : d206395 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150127, d206395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150127, d206395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150131 q = 1) (hb : d202307 q = 1) : d206399 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150131, d206399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150131, d206399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48035 q ha hb
  have h12 (q : Pattern) (ha : d21607 q = 1) (hb : d202307 q = 1) : d206401 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21607, d206401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21607, d206401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48007 q ha hb
  have h13 (q : Pattern) (ha : d150132 q = 1) (hb : d202307 q = 1) : d206402 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150132, d206402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150132, d206402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150133 q = 1) (hb : d202307 q = 1) : d206403 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150133, d206403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150133, d206403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150134 q = 1) (hb : d202307 q = 1) : d206404 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150134, d206404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150134, d206404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d150135 q = 1) (hb : d202307 q = 1) : d206405 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150135, d206405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150135, d206405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150141 q = 1) (hb : d202307 q = 1) : d206458 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150141, d206458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150141, d206458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48044 q ha hb
  have h18 (q : Pattern) (ha : d21722 q = 1) (hb : d202307 q = 1) : d206469 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21722, d206469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21722, d206469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48012 q ha hb
  have h19 (q : Pattern) (ha : d150142 q = 1) (hb : d202307 q = 1) : d206470 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150142, d206470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150142, d206470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d150143 q = 1) (hb : d202307 q = 1) : d206471 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150143, d206471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150143, d206471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d150144 q = 1) (hb : d202307 q = 1) : d206472 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150144, d206472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150144, d206472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d150145 q = 1) (hb : d202307 q = 1) : d206473 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150145, d206473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150145, d206473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d150146 q = 1) (hb : d202307 q = 1) : d206474 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150146, d206474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150146, d206474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro48046 (p : Pattern) (ha : d150152 p = 1) (hb : d202307 p = 1) : d206480 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150147 q = 1) (hb : d202307 q = 1) : d206475 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150147, d206475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150147, d206475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48045 q ha hb
  have h2 (q : Pattern) (ha : d150148 q = 1) (hb : d202307 q = 1) : d206476 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150148, d206476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150148, d206476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150149 q = 1) (hb : d202307 q = 1) : d206477 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150149, d206477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150149, d206477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150150 q = 1) (hb : d202307 q = 1) : d206478 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150150, d206478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150150, d206478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150151 q = 1) (hb : d202307 q = 1) : d206479 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150151, d206479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150151, d206479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150152 q = 1) (hb : d202307 q = 1) : d206480 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150152, d206480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150152, d206480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48047 (p : Pattern) (ha : d13024 p = 1) (hb : d202307 p = 1) : d206134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1095 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9452 q = 1) (hb : d202304 q = 1) : d206129 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d206129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47968 q ha hb
    | true =>
      simp only [d9452, d206129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9453 q = 1) (hb : d202304 q = 1) : d206130 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d206130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9453, d206130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d9795 q = 1) (hb : d202306 q = 1) : d206131 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9795, d202306, d206131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9795, d202306, d206131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9796 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d9796, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9797 q = 1) (hb : d202306 q = 1) : d206132 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9797, d206132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9797, d206132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9798 q = 1) (hb : d202306 q = 1) : d206133 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9798, d206133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9798, d206133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13024 q = 1) (hb : d202307 q = 1) : d206134 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13024, d202307, d206134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13024, d202307, d206134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48048 (p : Pattern) (ha : d1087 p = 1) (hb : d202304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1086 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1087 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d1087, d202304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1087, d202304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48049 (p : Pattern) (ha : d21736 p = 1) (hb : d202307 p = 1) : d206311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d823 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1088 q = 1) (hb : d202304 q = 1) : d30967 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48017 q ha hb
    | true =>
      simp only [d1088, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48048 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1089 q = 1) (hb : d202304 q = 1) : d30968 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1089, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1090 q = 1) (hb : d202306 q = 1) : d206307 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1090, d202306, d206307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1090, d202306, d206307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d829 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d537 q = 1) (hb : d202304 q = 1) : d30971 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d30971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48018 q ha hb
    | true =>
      simp only [d537, d30971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d538 q = 1) (hb : d202304 q = 1) : d30972 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d30972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d538, d30972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d830 q = 1) (hb : d202306 q = 1) : d206308 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d830, d202306, d206308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d830, d202306, d206308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1091 q = 1) (hb : d202306 q = 1) : d206309 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1091, d206309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1091, d206309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1092 q = 1) (hb : d202306 q = 1) : d206310 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1092, d206310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1092, d206310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21736 q = 1) (hb : d202307 q = 1) : d206311 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21736, d202307, d206311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21736, d202307, d206311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro48050 (p : Pattern) (ha : d1093 p = 1) (hb : d202304 p = 1) : d9771 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1086 q = 1) : d1086 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1093 q = 1) (hb : d202304 q = 1) : d9771 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d1093, d202304, d9771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1093, d202304, d9771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48051 (p : Pattern) (ha : d21741 p = 1) (hb : d202307 p = 1) : d206486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1094 q = 1) (hb : d202304 q = 1) : d31621 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d31621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47966 q ha hb
    | true =>
      simp only [d1094, d31621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48050 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1095 q = 1) (hb : d202304 q = 1) : d31622 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d31622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1095, d31622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1096 q = 1) (hb : d202306 q = 1) : d206483 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1096, d202306, d206483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1096, d202306, d206483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d538 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d133 q = 1) (hb : d202304 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d134 q = 1) (hb : d202304 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d539 q = 1) (hb : d202306 q = 1) : d205998 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d202306, d205998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d539, d202306, d205998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1097 q = 1) (hb : d202306 q = 1) : d206484 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1097, d206484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1097, d206484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1098 q = 1) (hb : d202306 q = 1) : d206485 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1098, d206485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1098, d206485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21741 q = 1) (hb : d202307 q = 1) : d206486 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21741, d202307, d206486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21741, d202307, d206486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro48052 (p : Pattern) (ha : d21747 p = 1) (hb : d202307 p = 1) : d206323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9581 q = 1) (hb : d202304 q = 1) : d206318 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9581, d206318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48020 q ha hb
    | true =>
      simp only [d9581, d206318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9582 q = 1) (hb : d202304 q = 1) : d206319 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d206319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9582, d206319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d9768 q = 1) (hb : d202306 q = 1) : d206320 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9768, d202306, d206320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9768, d202306, d206320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9769 q = 1) (hb : d202306 q = 1) : d206321 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9769, d206321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9769, d206321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9770 q = 1) (hb : d202306 q = 1) : d206322 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9770, d206322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9770, d206322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d21747 q = 1) (hb : d202307 q = 1) : d206323 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21747, d202307, d206323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21747, d202307, d206323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro48053 (p : Pattern) (ha : d21753 p = 1) (hb : d202307 p = 1) : d206492 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21737 q = 1) (hb : d202307 q = 1) : d206312 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21737, d206312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48049 q ha hb
    | true =>
      simp only [d21737, d206312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21738 q = 1) (hb : d202307 q = 1) : d206313 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21738, d206313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21738, d206313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21739 q = 1) (hb : d202307 q = 1) : d206314 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21739, d206314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21739, d206314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21740 q = 1) (hb : d202307 q = 1) : d206315 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21740, d206315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21740, d206315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21742 q = 1) (hb : d202307 q = 1) : d206487 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d206487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48051 q ha hb
    | true =>
      simp only [d21742, d206487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21743 q = 1) (hb : d202307 q = 1) : d206488 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d206488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21743, d206488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21744 q = 1) (hb : d202307 q = 1) : d206489 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21744, d206489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21744, d206489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21745 q = 1) (hb : d202307 q = 1) : d206490 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21745, d206490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21745, d206490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21746 q = 1) (hb : d202307 q = 1) : d206491 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21746, d206491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21746, d206491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21748 q = 1) (hb : d202307 q = 1) : d206324 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21748, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48052 q ha hb
    | true =>
      simp only [d21748, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21749 q = 1) (hb : d202307 q = 1) : d206325 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21749, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21749, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21750 q = 1) (hb : d202307 q = 1) : d206326 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21750, d206326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21750, d206326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21751 q = 1) (hb : d202307 q = 1) : d206327 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21751, d206327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21751, d206327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d13025 q = 1) (hb : d202307 q = 1) : d206135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48047 q ha hb
    | true =>
      simp only [d13025, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d13026 q = 1) (hb : d202307 q = 1) : d206136 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d13026, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d13027 q = 1) (hb : d202307 q = 1) : d206137 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13027, d206137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13027, d206137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13028 q = 1) (hb : d202307 q = 1) : d206138 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13028, d206138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13028, d206138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21752 q = 1) (hb : d202307 q = 1) : d206328 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21752, d206328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21752, d206328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21753 q = 1) (hb : d202307 q = 1) : d206492 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21753, d206492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21753, d206492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro48054 (p : Pattern) (ha : d21754 p = 1) (hb : d202307 p = 1) : d206496 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1095 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18 q = 1) (hb : d202304 q = 1) : d18 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1104 q = 1) (hb : d202304 q = 1) : d31656 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1104, d31656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d1104, d31656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1105 q = 1) (hb : d202304 q = 1) : d31657 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1105, d31657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1105, d31657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1106 q = 1) (hb : d202306 q = 1) : d206493 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1106, d202306, d206493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1106, d202306, d206493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d202304 q = 1) : d20 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d135 q = 1) (hb : d202306 q = 1) : d29090 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d202306, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d135, d202306, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1107 q = 1) (hb : d202306 q = 1) : d206494 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1107, d206494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1107, d206494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1108 q = 1) (hb : d202306 q = 1) : d206495 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1108, d206495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1108, d206495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21754 q = 1) (hb : d202307 q = 1) : d206496 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21754, d202307, d206496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21754, d202307, d206496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro48055 (p : Pattern) (ha : d21761 p = 1) (hb : d202307 p = 1) : d206503 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21742 q = 1) (hb : d202307 q = 1) : d206487 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d206487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48051 q ha hb
    | true =>
      simp only [d21742, d206487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21743 q = 1) (hb : d202307 q = 1) : d206488 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d206488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21743, d206488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21744 q = 1) (hb : d202307 q = 1) : d206489 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21744, d206489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21744, d206489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21745 q = 1) (hb : d202307 q = 1) : d206490 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21745, d206490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21745, d206490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21755 q = 1) (hb : d202307 q = 1) : d206497 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d206497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48054 q ha hb
    | true =>
      simp only [d21755, d206497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21756 q = 1) (hb : d202307 q = 1) : d206498 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d206498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21756, d206498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21757 q = 1) (hb : d202307 q = 1) : d206499 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21757, d206499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21757, d206499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21758 q = 1) (hb : d202307 q = 1) : d206500 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21758, d206500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21758, d206500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21759 q = 1) (hb : d202307 q = 1) : d206501 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21759, d206501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21759, d206501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13025 q = 1) (hb : d202307 q = 1) : d206135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48047 q ha hb
    | true =>
      simp only [d13025, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13026 q = 1) (hb : d202307 q = 1) : d206136 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13026, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13027 q = 1) (hb : d202307 q = 1) : d206137 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13027, d206137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13027, d206137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13028 q = 1) (hb : d202307 q = 1) : d206138 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13028, d206138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13028, d206138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d21760 q = 1) (hb : d202307 q = 1) : d206502 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21760, d206502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21760, d206502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d21761 q = 1) (hb : d202307 q = 1) : d206503 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21761, d206503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21761, d206503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48056 (p : Pattern) (ha : d9843 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1116 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1132 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1132, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1132, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d21 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d21, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9841 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9842 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9843 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9843, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9843, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro48057 (p : Pattern) (ha : d21765 p = 1) (hb : d202307 p = 1) : d206512 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1095 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18 q = 1) (hb : d202304 q = 1) : d18 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5012 q = 1) (hb : d202304 q = 1) : d206507 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5012, d206507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47968 q ha hb
    | true =>
      simp only [d5012, d206507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5013 q = 1) (hb : d202304 q = 1) : d206508 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5013, d206508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5013, d206508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5014 q = 1) (hb : d202306 q = 1) : d206509 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5014, d202306, d206509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5014, d202306, d206509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d202304 q = 1) : d20 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d135 q = 1) (hb : d202306 q = 1) : d29090 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d202306, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d135, d202306, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5015 q = 1) (hb : d202306 q = 1) : d206510 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5015, d206510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5015, d206510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5016 q = 1) (hb : d202306 q = 1) : d206511 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5016, d206511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5016, d206511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21765 q = 1) (hb : d202307 q = 1) : d206512 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21765, d202307, d206512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21765, d202307, d206512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro48058 (p : Pattern) (ha : d21771 p = 1) (hb : d202307 p = 1) : d206518 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21766 q = 1) (hb : d202307 q = 1) : d206513 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21766, d206513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48057 q ha hb
    | true =>
      simp only [d21766, d206513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21767 q = 1) (hb : d202307 q = 1) : d206514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21767, d206514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21767, d206514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21768 q = 1) (hb : d202307 q = 1) : d206515 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21768, d206515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21768, d206515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21769 q = 1) (hb : d202307 q = 1) : d206516 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21769, d206516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21769, d206516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21770 q = 1) (hb : d202307 q = 1) : d206517 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21770, d206517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21770, d206517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9844 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48056 q ha hb
    | true =>
      simp only [d9844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9846 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14770 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14771 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14772 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21771 q = 1) (hb : d202307 q = 1) : d206518 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21771, d206518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21771, d206518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48059 (p : Pattern) (ha : d21777 p = 1) (hb : d202307 p = 1) : d206524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21755 q = 1) (hb : d202307 q = 1) : d206497 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d206497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48054 q ha hb
    | true =>
      simp only [d21755, d206497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21756 q = 1) (hb : d202307 q = 1) : d206498 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d206498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21756, d206498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21757 q = 1) (hb : d202307 q = 1) : d206499 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21757, d206499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21757, d206499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21758 q = 1) (hb : d202307 q = 1) : d206500 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21758, d206500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21758, d206500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21776 q = 1) (hb : d202307 q = 1) : d206523 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21776, d206523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21776, d206523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9844 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48056 q ha hb
    | true =>
      simp only [d9844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9846 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14770 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14771 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14772 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21777 q = 1) (hb : d202307 q = 1) : d206524 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21777, d206524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21777, d206524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48060 (p : Pattern) (ha : d21783 p = 1) (hb : d202307 p = 1) : d206530 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21762 q = 1) (hb : d202307 q = 1) : d206504 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21762, d206504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48053 q ha hb
    | true =>
      simp only [d21762, d206504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48055 q ha hb
  have h2 (q : Pattern) (ha : d21763 q = 1) (hb : d202307 q = 1) : d206505 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21763, d206505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21763, d206505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21764 q = 1) (hb : d202307 q = 1) : d206506 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21764, d206506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21764, d206506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21772 q = 1) (hb : d202307 q = 1) : d206519 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21772, d206519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48055 q ha hb
    | true =>
      simp only [d21772, d206519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48058 q ha hb
  have h5 (q : Pattern) (ha : d21773 q = 1) (hb : d202307 q = 1) : d206520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21773, d206520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21773, d206520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21774 q = 1) (hb : d202307 q = 1) : d206521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21774, d206521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21774, d206521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21775 q = 1) (hb : d202307 q = 1) : d206522 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21775, d206522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21775, d206522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21778 q = 1) (hb : d202307 q = 1) : d206525 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21778, d206525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48055 q ha hb
    | true =>
      simp only [d21778, d206525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48059 q ha hb
  have h9 (q : Pattern) (ha : d21779 q = 1) (hb : d202307 q = 1) : d206526 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21779, d206526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21779, d206526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21780 q = 1) (hb : d202307 q = 1) : d206527 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21780, d206527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21780, d206527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21781 q = 1) (hb : d202307 q = 1) : d206528 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21781, d206528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21781, d206528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21782 q = 1) (hb : d202307 q = 1) : d206529 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21782, d206529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21782, d206529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21783 q = 1) (hb : d202307 q = 1) : d206530 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21783, d206530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21783, d206530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro48061 (p : Pattern) (ha : d21787 p = 1) (hb : d202307 p = 1) : d206534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21778 q = 1) (hb : d202307 q = 1) : d206525 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21778, d206525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48055 q ha hb
    | true =>
      simp only [d21778, d206525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48059 q ha hb
  have h2 (q : Pattern) (ha : d21779 q = 1) (hb : d202307 q = 1) : d206526 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21779, d206526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21779, d206526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21780 q = 1) (hb : d202307 q = 1) : d206527 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21780, d206527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21780, d206527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21781 q = 1) (hb : d202307 q = 1) : d206528 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21781, d206528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21781, d206528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21786 q = 1) (hb : d202307 q = 1) : d206533 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21786, d206533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21786, d206533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21787 q = 1) (hb : d202307 q = 1) : d206534 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21787, d206534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21787, d206534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48062 (p : Pattern) (ha : d21793 p = 1) (hb : d202307 p = 1) : d206540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d202307 q = 1) : d206531 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d206531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48060 q ha hb
    | true =>
      simp only [d21784, d206531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d202307 q = 1) : d206532 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d206532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d206532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d202307 q = 1) : d206535 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48061 q ha hb
    | true =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d202307 q = 1) : d206536 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d202307 q = 1) : d206537 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d206537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d206537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d202307 q = 1) : d206538 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d206538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d206538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21792 q = 1) (hb : d202307 q = 1) : d206539 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21792, d206539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21792, d206539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21793 q = 1) (hb : d202307 q = 1) : d206540 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21793, d206540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21793, d206540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48063 (p : Pattern) (ha : d21797 p = 1) (hb : d202307 p = 1) : d206544 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d202307 q = 1) : d206535 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48061 q ha hb
    | true =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d202307 q = 1) : d206536 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d202307 q = 1) : d206541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d206541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d206541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d202307 q = 1) : d206542 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d206542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d206542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21796 q = 1) (hb : d202307 q = 1) : d206543 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21796, d206543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21796, d206543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21797 q = 1) (hb : d202307 q = 1) : d206544 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21797, d206544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21797, d206544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48064 (p : Pattern) (ha : d21803 p = 1) (hb : d202307 p = 1) : d206550 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21798 q = 1) (hb : d202307 q = 1) : d206545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21798, d206545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48062 q ha hb
    | true =>
      simp only [d21798, d206545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48063 q ha hb
  have h2 (q : Pattern) (ha : d21799 q = 1) (hb : d202307 q = 1) : d206546 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21799, d206546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21799, d206546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21800 q = 1) (hb : d202307 q = 1) : d206547 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21800, d206547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21800, d206547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21801 q = 1) (hb : d202307 q = 1) : d206548 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21801, d206548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21801, d206548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21802 q = 1) (hb : d202307 q = 1) : d206549 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21802, d206549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21802, d206549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21803 q = 1) (hb : d202307 q = 1) : d206550 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21803, d206550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21803, d206550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48065 (p : Pattern) (ha : d21806 p = 1) (hb : d202307 p = 1) : d206553 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d202307 q = 1) : d206531 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d206531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48060 q ha hb
    | true =>
      simp only [d21784, d206531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d202307 q = 1) : d206532 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d206532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d206532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d202307 q = 1) : d206535 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48061 q ha hb
    | true =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d202307 q = 1) : d206536 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d202307 q = 1) : d206537 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d206537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d206537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d202307 q = 1) : d206538 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d206538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d206538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21792 q = 1) (hb : d202307 q = 1) : d206539 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21792, d206539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21792, d206539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21806 q = 1) (hb : d202307 q = 1) : d206553 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21806, d206553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21806, d206553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48066 (p : Pattern) (ha : d21807 p = 1) (hb : d202307 p = 1) : d206554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d202307 q = 1) : d206535 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48061 q ha hb
    | true =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d202307 q = 1) : d206536 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d202307 q = 1) : d206541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d206541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d206541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d202307 q = 1) : d206542 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d206542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d206542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21796 q = 1) (hb : d202307 q = 1) : d206543 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21796, d206543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21796, d206543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21807 q = 1) (hb : d202307 q = 1) : d206554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21807, d206554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21807, d206554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48067 (p : Pattern) (ha : d21813 p = 1) (hb : d202307 p = 1) : d206560 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21798 q = 1) (hb : d202307 q = 1) : d206545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21798, d206545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48062 q ha hb
    | true =>
      simp only [d21798, d206545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48063 q ha hb
  have h2 (q : Pattern) (ha : d21799 q = 1) (hb : d202307 q = 1) : d206546 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21799, d206546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21799, d206546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21800 q = 1) (hb : d202307 q = 1) : d206547 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21800, d206547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21800, d206547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21801 q = 1) (hb : d202307 q = 1) : d206548 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21801, d206548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21801, d206548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21802 q = 1) (hb : d202307 q = 1) : d206549 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21802, d206549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21802, d206549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21808 q = 1) (hb : d202307 q = 1) : d206555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21808, d206555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48065 q ha hb
    | true =>
      simp only [d21808, d206555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48066 q ha hb
  have h7 (q : Pattern) (ha : d21809 q = 1) (hb : d202307 q = 1) : d206556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21809, d206556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21809, d206556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21810 q = 1) (hb : d202307 q = 1) : d206557 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21810, d206557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21810, d206557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21811 q = 1) (hb : d202307 q = 1) : d206558 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21811, d206558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21811, d206558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21812 q = 1) (hb : d202307 q = 1) : d206559 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21812, d206559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21812, d206559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21813 q = 1) (hb : d202307 q = 1) : d206560 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21813, d206560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21813, d206560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48068 (p : Pattern) (ha : d21867 p = 1) (hb : d202307 p = 1) : d206617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21762 q = 1) (hb : d202307 q = 1) : d206504 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21762, d206504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48053 q ha hb
    | true =>
      simp only [d21762, d206504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48055 q ha hb
  have h2 (q : Pattern) (ha : d21763 q = 1) (hb : d202307 q = 1) : d206505 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21763, d206505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21763, d206505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21764 q = 1) (hb : d202307 q = 1) : d206506 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21764, d206506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21764, d206506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21772 q = 1) (hb : d202307 q = 1) : d206519 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21772, d206519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48055 q ha hb
    | true =>
      simp only [d21772, d206519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48058 q ha hb
  have h5 (q : Pattern) (ha : d21773 q = 1) (hb : d202307 q = 1) : d206520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21773, d206520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21773, d206520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21774 q = 1) (hb : d202307 q = 1) : d206521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21774, d206521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21774, d206521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21775 q = 1) (hb : d202307 q = 1) : d206522 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21775, d206522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21775, d206522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21865 q = 1) (hb : d202307 q = 1) : d206615 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21865, d206615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21865, d206615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21866 q = 1) (hb : d202307 q = 1) : d206616 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21866, d206616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21866, d206616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21867 q = 1) (hb : d202307 q = 1) : d206617 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21867, d206617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21867, d206617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro48069 (p : Pattern) (ha : d21877 p = 1) (hb : d202307 p = 1) : d206627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21868 q = 1) (hb : d202307 q = 1) : d206618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21868, d206618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48068 q ha hb
    | true =>
      simp only [d21868, d206618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21869 q = 1) (hb : d202307 q = 1) : d206619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21869, d206619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21869, d206619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d202307 q = 1) : d206535 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48061 q ha hb
    | true =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d202307 q = 1) : d206536 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21874 q = 1) (hb : d202307 q = 1) : d206624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21874, d206624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21874, d206624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21875 q = 1) (hb : d202307 q = 1) : d206625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21875, d206625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21875, d206625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21876 q = 1) (hb : d202307 q = 1) : d206626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21876, d206626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21876, d206626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21877 q = 1) (hb : d202307 q = 1) : d206627 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21877, d206627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21877, d206627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48070 (p : Pattern) (ha : d22003 p = 1) (hb : d202307 p = 1) : d206673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21993 q = 1) (hb : d202307 q = 1) : d206663 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21993, d206663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48069 q ha hb
    | true =>
      simp only [d21993, d206663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48063 q ha hb
  have h2 (q : Pattern) (ha : d21994 q = 1) (hb : d202307 q = 1) : d206664 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21994, d206664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21994, d206664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21995 q = 1) (hb : d202307 q = 1) : d206665 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21995, d206665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21995, d206665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21996 q = 1) (hb : d202307 q = 1) : d206666 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21996, d206666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21996, d206666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21997 q = 1) (hb : d202307 q = 1) : d206667 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21997, d206667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21997, d206667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21998 q = 1) (hb : d202307 q = 1) : d206668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21998, d206668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48063 q ha hb
    | true =>
      simp only [d21998, d206668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21999 q = 1) (hb : d202307 q = 1) : d206669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21999, d206669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21999, d206669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22000 q = 1) (hb : d202307 q = 1) : d206670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22000, d206670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22000, d206670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22001 q = 1) (hb : d202307 q = 1) : d206671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22001, d206671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22001, d206671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22002 q = 1) (hb : d202307 q = 1) : d206672 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22002, d206672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22002, d206672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22003 q = 1) (hb : d202307 q = 1) : d206673 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22003, d206673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22003, d206673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48071 (p : Pattern) (ha : d22009 p = 1) (hb : d202307 p = 1) : d206679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21998 q = 1) (hb : d202307 q = 1) : d206668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21998, d206668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48063 q ha hb
    | true =>
      simp only [d21998, d206668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21999 q = 1) (hb : d202307 q = 1) : d206669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21999, d206669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21999, d206669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22000 q = 1) (hb : d202307 q = 1) : d206670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22000, d206670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22000, d206670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22001 q = 1) (hb : d202307 q = 1) : d206671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22001, d206671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22001, d206671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22002 q = 1) (hb : d202307 q = 1) : d206672 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22002, d206672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22002, d206672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22004 q = 1) (hb : d202307 q = 1) : d206674 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22004, d206674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48066 q ha hb
    | true =>
      simp only [d22004, d206674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22005 q = 1) (hb : d202307 q = 1) : d206675 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22005, d206675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22005, d206675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22006 q = 1) (hb : d202307 q = 1) : d206676 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22006, d206676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22006, d206676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22007 q = 1) (hb : d202307 q = 1) : d206677 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22007, d206677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22007, d206677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22008 q = 1) (hb : d202307 q = 1) : d206678 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22008, d206678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22008, d206678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22009 q = 1) (hb : d202307 q = 1) : d206679 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22009, d206679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22009, d206679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48072 (p : Pattern) (ha : d22018 p = 1) (hb : d202307 p = 1) : d206688 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22004 q = 1) (hb : d202307 q = 1) : d206674 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22004, d206674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48066 q ha hb
    | true =>
      simp only [d22004, d206674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22005 q = 1) (hb : d202307 q = 1) : d206675 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22005, d206675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22005, d206675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22006 q = 1) (hb : d202307 q = 1) : d206676 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22006, d206676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22006, d206676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22007 q = 1) (hb : d202307 q = 1) : d206677 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22007, d206677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22007, d206677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22008 q = 1) (hb : d202307 q = 1) : d206678 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22008, d206678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22008, d206678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22018 q = 1) (hb : d202307 q = 1) : d206688 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22018, d206688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22018, d206688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48073 (p : Pattern) (ha : d22069 p = 1) (hb : d202307 p = 1) : d206726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22043 q = 1) (hb : d202307 q = 1) : d206701 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22043, d206701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22043, d206701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48051 q ha hb
  have h2 (q : Pattern) (ha : d21742 q = 1) (hb : d202307 q = 1) : d206487 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d206487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48051 q ha hb
    | true =>
      simp only [d21742, d206487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22044 q = 1) (hb : d202307 q = 1) : d206702 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22044, d206702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22044, d206702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21743 q = 1) (hb : d202307 q = 1) : d206488 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d206488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21743, d206488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22045 q = 1) (hb : d202307 q = 1) : d206703 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22045, d206703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22045, d206703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22046 q = 1) (hb : d202307 q = 1) : d206704 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22046, d206704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22046, d206704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22064 q = 1) (hb : d202307 q = 1) : d206721 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22064, d206721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22064, d206721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48054 q ha hb
  have h8 (q : Pattern) (ha : d21755 q = 1) (hb : d202307 q = 1) : d206497 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d206497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48054 q ha hb
    | true =>
      simp only [d21755, d206497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22065 q = 1) (hb : d202307 q = 1) : d206722 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22065, d206722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22065, d206722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21756 q = 1) (hb : d202307 q = 1) : d206498 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d206498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21756, d206498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22066 q = 1) (hb : d202307 q = 1) : d206723 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22066, d206723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22066, d206723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22067 q = 1) (hb : d202307 q = 1) : d206724 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22067, d206724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22067, d206724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22068 q = 1) (hb : d202307 q = 1) : d206725 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22068, d206725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22068, d206725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13164 q = 1) (hb : d202307 q = 1) : d206205 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13164, d206205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13164, d206205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48047 q ha hb
  have h15 (q : Pattern) (ha : d13025 q = 1) (hb : d202307 q = 1) : d206135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48047 q ha hb
    | true =>
      simp only [d13025, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d13165 q = 1) (hb : d202307 q = 1) : d206206 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13165, d206206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d13165, d206206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13026 q = 1) (hb : d202307 q = 1) : d206136 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13026, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13166 q = 1) (hb : d202307 q = 1) : d206207 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13166, d206207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13166, d206207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13167 q = 1) (hb : d202307 q = 1) : d206208 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13167, d206208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d13167, d206208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d22058 q = 1) (hb : d202307 q = 1) : d206715 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22058, d206715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d22058, d206715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d22069 q = 1) (hb : d202307 q = 1) : d206726 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22069, d206726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22069, d206726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro48074 (p : Pattern) (ha : d22097 p = 1) (hb : d202307 p = 1) : d206754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22064 q = 1) (hb : d202307 q = 1) : d206721 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22064, d206721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22064, d206721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48054 q ha hb
  have h2 (q : Pattern) (ha : d21755 q = 1) (hb : d202307 q = 1) : d206497 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d206497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48054 q ha hb
    | true =>
      simp only [d21755, d206497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22065 q = 1) (hb : d202307 q = 1) : d206722 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22065, d206722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22065, d206722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21756 q = 1) (hb : d202307 q = 1) : d206498 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d206498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21756, d206498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22066 q = 1) (hb : d202307 q = 1) : d206723 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22066, d206723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22066, d206723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22067 q = 1) (hb : d202307 q = 1) : d206724 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22067, d206724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22067, d206724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22096 q = 1) (hb : d202307 q = 1) : d206753 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22096, d206753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22096, d206753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15019 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48056 q ha hb
  have h9 (q : Pattern) (ha : d9844 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48056 q ha hb
    | true =>
      simp only [d9844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15020 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9846 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15021 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15022 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15023 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22097 q = 1) (hb : d202307 q = 1) : d206754 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22097, d206754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22097, d206754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48075 (p : Pattern) (ha : d22103 p = 1) (hb : d202307 p = 1) : d206760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22098 q = 1) (hb : d202307 q = 1) : d206755 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22098, d206755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48073 q ha hb
    | true =>
      simp only [d22098, d206755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48074 q ha hb
  have h2 (q : Pattern) (ha : d22099 q = 1) (hb : d202307 q = 1) : d206756 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22099, d206756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22099, d206756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22100 q = 1) (hb : d202307 q = 1) : d206757 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22100, d206757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22100, d206757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22101 q = 1) (hb : d202307 q = 1) : d206758 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22101, d206758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22101, d206758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22102 q = 1) (hb : d202307 q = 1) : d206759 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22102, d206759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22102, d206759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22103 q = 1) (hb : d202307 q = 1) : d206760 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22103, d206760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22103, d206760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48076 (p : Pattern) (ha : d22197 p = 1) (hb : d202307 p = 1) : d206787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22104 q = 1) (hb : d202307 q = 1) : d206761 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22104, d206761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48075 q ha hb
    | true =>
      simp only [d22104, d206761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22105 q = 1) (hb : d202307 q = 1) : d206762 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22105, d206762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22105, d206762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22194 q = 1) (hb : d202307 q = 1) : d206784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22194, d206784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22194, d206784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22195 q = 1) (hb : d202307 q = 1) : d206785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22195, d206785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22195, d206785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22196 q = 1) (hb : d202307 q = 1) : d206786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22196, d206786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22196, d206786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22197 q = 1) (hb : d202307 q = 1) : d206787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22197, d206787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22197, d206787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48077 (p : Pattern) (ha : d22203 p = 1) (hb : d202307 p = 1) : d206793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22198 q = 1) (hb : d202307 q = 1) : d206788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22198, d206788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48076 q ha hb
    | true =>
      simp only [d22198, d206788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22199 q = 1) (hb : d202307 q = 1) : d206789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22199, d206789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22199, d206789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22200 q = 1) (hb : d202307 q = 1) : d206790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22200, d206790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22200, d206790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22201 q = 1) (hb : d202307 q = 1) : d206791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22201, d206791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22201, d206791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22202 q = 1) (hb : d202307 q = 1) : d206792 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22202, d206792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22202, d206792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22203 q = 1) (hb : d202307 q = 1) : d206793 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22203, d206793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22203, d206793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48078 (p : Pattern) (ha : d21818 p = 1) (hb : d202307 p = 1) : d206565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d202307 q = 1) : d206531 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d206531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48060 q ha hb
    | true =>
      simp only [d21784, d206531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d202307 q = 1) : d206532 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d206532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d206532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d202307 q = 1) : d206535 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48061 q ha hb
    | true =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d202307 q = 1) : d206536 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d202307 q = 1) : d206537 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d206537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d206537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d202307 q = 1) : d206538 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d206538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d206538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21817 q = 1) (hb : d202307 q = 1) : d206564 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21817, d206564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21817, d206564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21818 q = 1) (hb : d202307 q = 1) : d206565 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21818, d206565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21818, d206565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48079 (p : Pattern) (ha : d21820 p = 1) (hb : d202307 p = 1) : d206567 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d202307 q = 1) : d206535 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48061 q ha hb
    | true =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d202307 q = 1) : d206536 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d202307 q = 1) : d206541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d206541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d206541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d202307 q = 1) : d206542 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d206542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d206542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21819 q = 1) (hb : d202307 q = 1) : d206566 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21819, d206566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21819, d206566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21820 q = 1) (hb : d202307 q = 1) : d206567 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21820, d206567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21820, d206567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48080 (p : Pattern) (ha : d21827 p = 1) (hb : d202307 p = 1) : d206574 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d202307 q = 1) : d206531 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d206531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48060 q ha hb
    | true =>
      simp only [d21784, d206531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d202307 q = 1) : d206532 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d206532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d206532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d202307 q = 1) : d206535 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48061 q ha hb
    | true =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d202307 q = 1) : d206536 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d202307 q = 1) : d206537 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d206537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d206537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21825 q = 1) (hb : d202307 q = 1) : d206572 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21825, d206572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21825, d206572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21826 q = 1) (hb : d202307 q = 1) : d206573 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21826, d206573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21826, d206573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21827 q = 1) (hb : d202307 q = 1) : d206574 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21827, d206574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21827, d206574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48081 (p : Pattern) (ha : d21830 p = 1) (hb : d202307 p = 1) : d206577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d202307 q = 1) : d206535 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48061 q ha hb
    | true =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d202307 q = 1) : d206536 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d202307 q = 1) : d206541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d206541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d206541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21828 q = 1) (hb : d202307 q = 1) : d206575 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21828, d206575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21828, d206575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21829 q = 1) (hb : d202307 q = 1) : d206576 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21829, d206576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21829, d206576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21830 q = 1) (hb : d202307 q = 1) : d206577 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21830, d206577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21830, d206577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48082 (p : Pattern) (ha : d821 p = 1) (hb : d202304 p = 1) : d31302 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d820 q = 1) : d820 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d529 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d821 q = 1) (hb : d202304 q = 1) : d31302 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d821, d202304, d31302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d821, d202304, d31302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48083 (p : Pattern) (ha : d827 p = 1) (hb : d202304 p = 1) : d28879 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d826 q = 1) : d826 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d535 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d827 q = 1) (hb : d202304 q = 1) : d28879 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d827, d202304, d28879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d827, d202304, d28879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48084 (p : Pattern) (ha : d21834 p = 1) (hb : d202307 p = 1) : d206584 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1201 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d822 q = 1) (hb : d202304 q = 1) : d31303 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d31303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48082 q ha hb
    | true =>
      simp only [d822, d31303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d823 q = 1) (hb : d202304 q = 1) : d31304 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d31304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d823, d31304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1202 q = 1) (hb : d202306 q = 1) : d31736 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1202, d202306, d31736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1202, d202306, d31736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1205 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d828 q = 1) (hb : d202304 q = 1) : d28880 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d828, d28880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48083 q ha hb
    | true =>
      simp only [d828, d28880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d829 q = 1) (hb : d202304 q = 1) : d28881 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d829, d28881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d829, d28881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1206 q = 1) (hb : d202306 q = 1) : d206581 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1206, d202306, d206581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1206, d202306, d206581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1207 q = 1) (hb : d202306 q = 1) : d206582 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1207, d206582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1207, d206582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1208 q = 1) (hb : d202306 q = 1) : d206583 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1208, d206583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1208, d206583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21834 q = 1) (hb : d202307 q = 1) : d206584 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21834, d202307, d206584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21834, d202307, d206584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro48085 (p : Pattern) (ha : d21840 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d823 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9759 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9759, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9759, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9760 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9761 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21840 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21840, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21840, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro48086 (p : Pattern) (ha : d21846 p = 1) (hb : d202307 p = 1) : d206591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21835 q = 1) (hb : d202307 q = 1) : d206585 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21835, d206585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48084 q ha hb
    | true =>
      simp only [d21835, d206585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21836 q = 1) (hb : d202307 q = 1) : d206586 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21836, d206586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21836, d206586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21837 q = 1) (hb : d202307 q = 1) : d206587 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21837, d206587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21837, d206587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21838 q = 1) (hb : d202307 q = 1) : d206588 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21838, d206588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21838, d206588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21737 q = 1) (hb : d202307 q = 1) : d206312 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21737, d206312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48049 q ha hb
    | true =>
      simp only [d21737, d206312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21738 q = 1) (hb : d202307 q = 1) : d206313 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21738, d206313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21738, d206313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21739 q = 1) (hb : d202307 q = 1) : d206314 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21739, d206314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21739, d206314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21740 q = 1) (hb : d202307 q = 1) : d206315 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21740, d206315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21740, d206315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21839 q = 1) (hb : d202307 q = 1) : d206589 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21839, d206589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21839, d206589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21841 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48085 q ha hb
    | true =>
      simp only [d21841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21842 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21843 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21844 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d21748 q = 1) (hb : d202307 q = 1) : d206324 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21748, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48052 q ha hb
    | true =>
      simp only [d21748, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d21749 q = 1) (hb : d202307 q = 1) : d206325 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21749, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d21749, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d21750 q = 1) (hb : d202307 q = 1) : d206326 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21750, d206326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21750, d206326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21751 q = 1) (hb : d202307 q = 1) : d206327 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21751, d206327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21751, d206327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21845 q = 1) (hb : d202307 q = 1) : d206590 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21845, d206590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21845, d206590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21846 q = 1) (hb : d202307 q = 1) : d206591 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21846, d206591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21846, d206591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro48087 (p : Pattern) (ha : d21850 p = 1) (hb : d202307 p = 1) : d206600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9771 q = 1) (hb : d202304 q = 1) : d9771 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9772 q = 1) (hb : d202304 q = 1) : d206595 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9772, d206595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48020 q ha hb
    | true =>
      simp only [d9772, d206595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9773 q = 1) (hb : d202304 q = 1) : d206596 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9773, d206596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9773, d206596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9810 q = 1) (hb : d202306 q = 1) : d206597 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9810, d202306, d206597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9810, d202306, d206597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9811 q = 1) (hb : d202306 q = 1) : d206598 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9811, d206598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9811, d206598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9812 q = 1) (hb : d202306 q = 1) : d206599 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9812, d206599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9812, d206599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21850 q = 1) (hb : d202307 q = 1) : d206600 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21850, d202307, d206600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21850, d202307, d206600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro48088 (p : Pattern) (ha : d21856 p = 1) (hb : d202307 p = 1) : d206606 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21851 q = 1) (hb : d202307 q = 1) : d206601 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21851, d206601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48087 q ha hb
    | true =>
      simp only [d21851, d206601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21852 q = 1) (hb : d202307 q = 1) : d206602 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21852, d206602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21852, d206602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21853 q = 1) (hb : d202307 q = 1) : d206603 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21853, d206603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21853, d206603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21854 q = 1) (hb : d202307 q = 1) : d206604 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21854, d206604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21854, d206604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13025 q = 1) (hb : d202307 q = 1) : d206135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48047 q ha hb
    | true =>
      simp only [d13025, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13026 q = 1) (hb : d202307 q = 1) : d206136 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13026, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13027 q = 1) (hb : d202307 q = 1) : d206137 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13027, d206137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13027, d206137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13028 q = 1) (hb : d202307 q = 1) : d206138 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13028, d206138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13028, d206138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21855 q = 1) (hb : d202307 q = 1) : d206605 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21855, d206605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21855, d206605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21760 q = 1) (hb : d202307 q = 1) : d206502 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21760, d206502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21760, d206502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21856 q = 1) (hb : d202307 q = 1) : d206606 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21856, d206606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21856, d206606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48089 (p : Pattern) (ha : d21862 p = 1) (hb : d202307 p = 1) : d206612 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21847 q = 1) (hb : d202307 q = 1) : d206592 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21847, d206592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48086 q ha hb
    | true =>
      simp only [d21847, d206592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48053 q ha hb
  have h2 (q : Pattern) (ha : d21848 q = 1) (hb : d202307 q = 1) : d206593 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21848, d206593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21848, d206593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21849 q = 1) (hb : d202307 q = 1) : d206594 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21849, d206594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21849, d206594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21857 q = 1) (hb : d202307 q = 1) : d206607 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21857, d206607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48053 q ha hb
    | true =>
      simp only [d21857, d206607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48088 q ha hb
  have h5 (q : Pattern) (ha : d21858 q = 1) (hb : d202307 q = 1) : d206608 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21858, d206608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21858, d206608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21859 q = 1) (hb : d202307 q = 1) : d206609 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21859, d206609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21859, d206609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21860 q = 1) (hb : d202307 q = 1) : d206610 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21860, d206610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21860, d206610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21762 q = 1) (hb : d202307 q = 1) : d206504 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21762, d206504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48053 q ha hb
    | true =>
      simp only [d21762, d206504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48055 q ha hb
  have h9 (q : Pattern) (ha : d21763 q = 1) (hb : d202307 q = 1) : d206505 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21763, d206505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21763, d206505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21764 q = 1) (hb : d202307 q = 1) : d206506 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21764, d206506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21764, d206506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21772 q = 1) (hb : d202307 q = 1) : d206519 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21772, d206519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48055 q ha hb
    | true =>
      simp only [d21772, d206519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48058 q ha hb
  have h12 (q : Pattern) (ha : d21773 q = 1) (hb : d202307 q = 1) : d206520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21773, d206520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21773, d206520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21774 q = 1) (hb : d202307 q = 1) : d206521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21774, d206521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21774, d206521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21775 q = 1) (hb : d202307 q = 1) : d206522 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21775, d206522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21775, d206522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21861 q = 1) (hb : d202307 q = 1) : d206611 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21861, d206611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21861, d206611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21862 q = 1) (hb : d202307 q = 1) : d206612 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21862, d206612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d21862, d206612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro48090 (p : Pattern) (ha : d21873 p = 1) (hb : d202307 p = 1) : d206623 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21863 q = 1) (hb : d202307 q = 1) : d206613 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21863, d206613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48089 q ha hb
    | true =>
      simp only [d21863, d206613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21864 q = 1) (hb : d202307 q = 1) : d206614 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21864, d206614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21864, d206614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21868 q = 1) (hb : d202307 q = 1) : d206618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21868, d206618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48068 q ha hb
    | true =>
      simp only [d21868, d206618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21869 q = 1) (hb : d202307 q = 1) : d206619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21869, d206619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21869, d206619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21870 q = 1) (hb : d202307 q = 1) : d206620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21870, d206620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21870, d206620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21871 q = 1) (hb : d202307 q = 1) : d206621 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21871, d206621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21871, d206621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21872 q = 1) (hb : d202307 q = 1) : d206622 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21872, d206622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21872, d206622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21873 q = 1) (hb : d202307 q = 1) : d206623 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21873, d206623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21873, d206623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48091 (p : Pattern) (ha : d21948 p = 1) (hb : d202307 p = 1) : d206524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21755 q = 1) (hb : d202307 q = 1) : d206497 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d206497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48054 q ha hb
    | true =>
      simp only [d21755, d206497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21756 q = 1) (hb : d202307 q = 1) : d206498 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d206498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21756, d206498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21757 q = 1) (hb : d202307 q = 1) : d206499 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21757, d206499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21757, d206499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21758 q = 1) (hb : d202307 q = 1) : d206500 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21758, d206500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21758, d206500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21776 q = 1) (hb : d202307 q = 1) : d206523 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21776, d206523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21776, d206523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21948 q = 1) (hb : d202307 q = 1) : d206524 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21948, d206524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21948, d206524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48092 (p : Pattern) (ha : d21954 p = 1) (hb : d202307 p = 1) : d206530 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21762 q = 1) (hb : d202307 q = 1) : d206504 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21762, d206504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48053 q ha hb
    | true =>
      simp only [d21762, d206504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48055 q ha hb
  have h2 (q : Pattern) (ha : d21763 q = 1) (hb : d202307 q = 1) : d206505 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21763, d206505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21763, d206505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21764 q = 1) (hb : d202307 q = 1) : d206506 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21764, d206506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21764, d206506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21772 q = 1) (hb : d202307 q = 1) : d206519 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21772, d206519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48055 q ha hb
    | true =>
      simp only [d21772, d206519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48058 q ha hb
  have h5 (q : Pattern) (ha : d21773 q = 1) (hb : d202307 q = 1) : d206520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21773, d206520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21773, d206520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21774 q = 1) (hb : d202307 q = 1) : d206521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21774, d206521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21774, d206521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21775 q = 1) (hb : d202307 q = 1) : d206522 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21775, d206522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21775, d206522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21949 q = 1) (hb : d202307 q = 1) : d206525 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21949, d206525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48055 q ha hb
    | true =>
      simp only [d21949, d206525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48091 q ha hb
  have h9 (q : Pattern) (ha : d21950 q = 1) (hb : d202307 q = 1) : d206526 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21950, d206526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21950, d206526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21951 q = 1) (hb : d202307 q = 1) : d206527 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21951, d206527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21951, d206527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21952 q = 1) (hb : d202307 q = 1) : d206528 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21952, d206528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21952, d206528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21953 q = 1) (hb : d202307 q = 1) : d206529 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21953, d206529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21953, d206529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21954 q = 1) (hb : d202307 q = 1) : d206530 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21954, d206530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21954, d206530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro48093 (p : Pattern) (ha : d21960 p = 1) (hb : d202307 p = 1) : d206633 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21955 q = 1) (hb : d202307 q = 1) : d206531 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21955, d206531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48092 q ha hb
    | true =>
      simp only [d21955, d206531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21956 q = 1) (hb : d202307 q = 1) : d206532 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21956, d206532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21956, d206532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21957 q = 1) (hb : d202307 q = 1) : d206630 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21957, d206630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21957, d206630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21958 q = 1) (hb : d202307 q = 1) : d206631 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21958, d206631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21958, d206631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21959 q = 1) (hb : d202307 q = 1) : d206632 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21959, d206632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21959, d206632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21960 q = 1) (hb : d202307 q = 1) : d206633 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21960, d206633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21960, d206633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48094 (p : Pattern) (ha : d150159 p = 1) (hb : d202307 p = 1) : d206639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21821 q = 1) (hb : d202307 q = 1) : d206568 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21821, d206568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48078 q ha hb
    | true =>
      simp only [d21821, d206568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48079 q ha hb
  have h2 (q : Pattern) (ha : d21822 q = 1) (hb : d202307 q = 1) : d206569 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21822, d206569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21822, d206569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21823 q = 1) (hb : d202307 q = 1) : d206570 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21823, d206570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21823, d206570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21824 q = 1) (hb : d202307 q = 1) : d206571 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21824, d206571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21824, d206571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21831 q = 1) (hb : d202307 q = 1) : d206578 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21831, d206578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48080 q ha hb
    | true =>
      simp only [d21831, d206578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48081 q ha hb
  have h6 (q : Pattern) (ha : d21832 q = 1) (hb : d202307 q = 1) : d206579 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21832, d206579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21832, d206579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21833 q = 1) (hb : d202307 q = 1) : d206580 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21833, d206580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21833, d206580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21878 q = 1) (hb : d202307 q = 1) : d206628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21878, d206628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48090 q ha hb
    | true =>
      simp only [d21878, d206628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48069 q ha hb
  have h9 (q : Pattern) (ha : d150155 q = 1) (hb : d202307 q = 1) : d206629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150155, d206629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150155, d206629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21961 q = 1) (hb : d202307 q = 1) : d206634 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21961, d206634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48093 q ha hb
    | true =>
      simp only [d21961, d206634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21962 q = 1) (hb : d202307 q = 1) : d206635 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21962, d206635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21962, d206635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150156 q = 1) (hb : d202307 q = 1) : d206636 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150156, d206636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150156, d206636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150157 q = 1) (hb : d202307 q = 1) : d206637 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150157, d206637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150157, d206637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150158 q = 1) (hb : d202307 q = 1) : d206638 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150158, d206638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150158, d206638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150159 q = 1) (hb : d202307 q = 1) : d206639 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150159, d206639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150159, d206639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48095 (p : Pattern) (ha : d21967 p = 1) (hb : d202307 p = 1) : d206640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d202307 q = 1) : d206531 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d206531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48060 q ha hb
    | true =>
      simp only [d21784, d206531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d202307 q = 1) : d206532 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d206532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d206532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d202307 q = 1) : d206535 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48061 q ha hb
    | true =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d202307 q = 1) : d206536 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d202307 q = 1) : d206537 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d206537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d206537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d202307 q = 1) : d206538 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d206538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d206538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21817 q = 1) (hb : d202307 q = 1) : d206564 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21817, d206564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21817, d206564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21967 q = 1) (hb : d202307 q = 1) : d206640 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21967, d206640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21967, d206640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48096 (p : Pattern) (ha : d21968 p = 1) (hb : d202307 p = 1) : d206641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d202307 q = 1) : d206535 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48061 q ha hb
    | true =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d202307 q = 1) : d206536 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d202307 q = 1) : d206541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d206541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d206541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d202307 q = 1) : d206542 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d206542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d206542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21819 q = 1) (hb : d202307 q = 1) : d206566 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21819, d206566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21819, d206566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21968 q = 1) (hb : d202307 q = 1) : d206641 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21968, d206641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21968, d206641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48097 (p : Pattern) (ha : d21973 p = 1) (hb : d202307 p = 1) : d206646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d202307 q = 1) : d206531 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d206531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48060 q ha hb
    | true =>
      simp only [d21784, d206531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d202307 q = 1) : d206532 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d206532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d206532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d202307 q = 1) : d206535 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48061 q ha hb
    | true =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d202307 q = 1) : d206536 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d202307 q = 1) : d206537 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d206537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d206537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21825 q = 1) (hb : d202307 q = 1) : d206572 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21825, d206572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21825, d206572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21826 q = 1) (hb : d202307 q = 1) : d206573 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21826, d206573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21826, d206573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21973 q = 1) (hb : d202307 q = 1) : d206646 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21973, d206646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21973, d206646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48098 (p : Pattern) (ha : d21974 p = 1) (hb : d202307 p = 1) : d206647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d202307 q = 1) : d206535 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48061 q ha hb
    | true =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d202307 q = 1) : d206536 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d202307 q = 1) : d206541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d206541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d206541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21828 q = 1) (hb : d202307 q = 1) : d206575 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21828, d206575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21828, d206575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21829 q = 1) (hb : d202307 q = 1) : d206576 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21829, d206576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21829, d206576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21974 q = 1) (hb : d202307 q = 1) : d206647 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21974, d206647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21974, d206647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48099 (p : Pattern) (ha : d21978 p = 1) (hb : d202307 p = 1) : d206651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21863 q = 1) (hb : d202307 q = 1) : d206613 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21863, d206613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48089 q ha hb
    | true =>
      simp only [d21863, d206613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21864 q = 1) (hb : d202307 q = 1) : d206614 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21864, d206614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21864, d206614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21868 q = 1) (hb : d202307 q = 1) : d206618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21868, d206618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48068 q ha hb
    | true =>
      simp only [d21868, d206618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21869 q = 1) (hb : d202307 q = 1) : d206619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21869, d206619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21869, d206619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21870 q = 1) (hb : d202307 q = 1) : d206620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21870, d206620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21870, d206620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21871 q = 1) (hb : d202307 q = 1) : d206621 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21871, d206621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21871, d206621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21872 q = 1) (hb : d202307 q = 1) : d206622 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21872, d206622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21872, d206622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21978 q = 1) (hb : d202307 q = 1) : d206651 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21978, d206651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21978, d206651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48100 (p : Pattern) (ha : d21979 p = 1) (hb : d202307 p = 1) : d206652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21868 q = 1) (hb : d202307 q = 1) : d206618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21868, d206618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48068 q ha hb
    | true =>
      simp only [d21868, d206618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21869 q = 1) (hb : d202307 q = 1) : d206619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21869, d206619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21869, d206619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d202307 q = 1) : d206535 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48061 q ha hb
    | true =>
      simp only [d21788, d206535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d202307 q = 1) : d206536 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d206536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21874 q = 1) (hb : d202307 q = 1) : d206624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21874, d206624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21874, d206624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21875 q = 1) (hb : d202307 q = 1) : d206625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21875, d206625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21875, d206625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21876 q = 1) (hb : d202307 q = 1) : d206626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21876, d206626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21876, d206626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21979 q = 1) (hb : d202307 q = 1) : d206652 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21979, d206652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21979, d206652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48101 (p : Pattern) (ha : d21985 p = 1) (hb : d202307 p = 1) : d206655 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21955 q = 1) (hb : d202307 q = 1) : d206531 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21955, d206531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48092 q ha hb
    | true =>
      simp only [d21955, d206531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21956 q = 1) (hb : d202307 q = 1) : d206532 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21956, d206532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21956, d206532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21957 q = 1) (hb : d202307 q = 1) : d206630 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21957, d206630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21957, d206630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21958 q = 1) (hb : d202307 q = 1) : d206631 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21958, d206631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21958, d206631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21959 q = 1) (hb : d202307 q = 1) : d206632 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21959, d206632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21959, d206632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21985 q = 1) (hb : d202307 q = 1) : d206655 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21985, d206655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21985, d206655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48102 (p : Pattern) (ha : d150164 p = 1) (hb : d202307 p = 1) : d206661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21821 q = 1) (hb : d202307 q = 1) : d206568 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21821, d206568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48078 q ha hb
    | true =>
      simp only [d21821, d206568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48079 q ha hb
  have h2 (q : Pattern) (ha : d21822 q = 1) (hb : d202307 q = 1) : d206569 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21822, d206569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21822, d206569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21823 q = 1) (hb : d202307 q = 1) : d206570 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21823, d206570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21823, d206570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21824 q = 1) (hb : d202307 q = 1) : d206571 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21824, d206571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21824, d206571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21831 q = 1) (hb : d202307 q = 1) : d206578 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21831, d206578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48080 q ha hb
    | true =>
      simp only [d21831, d206578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48081 q ha hb
  have h6 (q : Pattern) (ha : d21832 q = 1) (hb : d202307 q = 1) : d206579 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21832, d206579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21832, d206579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21833 q = 1) (hb : d202307 q = 1) : d206580 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21833, d206580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21833, d206580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21878 q = 1) (hb : d202307 q = 1) : d206628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21878, d206628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48090 q ha hb
    | true =>
      simp only [d21878, d206628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48069 q ha hb
  have h9 (q : Pattern) (ha : d150155 q = 1) (hb : d202307 q = 1) : d206629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150155, d206629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150155, d206629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21961 q = 1) (hb : d202307 q = 1) : d206634 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21961, d206634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48093 q ha hb
    | true =>
      simp only [d21961, d206634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21962 q = 1) (hb : d202307 q = 1) : d206635 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21962, d206635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21962, d206635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150156 q = 1) (hb : d202307 q = 1) : d206636 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150156, d206636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150156, d206636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150157 q = 1) (hb : d202307 q = 1) : d206637 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150157, d206637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150157, d206637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150158 q = 1) (hb : d202307 q = 1) : d206638 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150158, d206638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150158, d206638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21969 q = 1) (hb : d202307 q = 1) : d206642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21969, d206642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48095 q ha hb
    | true =>
      simp only [d21969, d206642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48096 q ha hb
  have h16 (q : Pattern) (ha : d21970 q = 1) (hb : d202307 q = 1) : d206643 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21970, d206643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21970, d206643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21971 q = 1) (hb : d202307 q = 1) : d206644 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21971, d206644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21971, d206644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21972 q = 1) (hb : d202307 q = 1) : d206645 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21972, d206645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21972, d206645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21975 q = 1) (hb : d202307 q = 1) : d206648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21975, d206648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48097 q ha hb
    | true =>
      simp only [d21975, d206648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48098 q ha hb
  have h20 (q : Pattern) (ha : d21976 q = 1) (hb : d202307 q = 1) : d206649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21976, d206649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21976, d206649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d21977 q = 1) (hb : d202307 q = 1) : d206650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21977, d206650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d21977, d206650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d21980 q = 1) (hb : d202307 q = 1) : d206653 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21980, d206653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48099 q ha hb
    | true =>
      simp only [d21980, d206653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48100 q ha hb
  have h23 (q : Pattern) (ha : d150160 q = 1) (hb : d202307 q = 1) : d206654 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150160, d206654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d150160, d206654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d21986 q = 1) (hb : d202307 q = 1) : d206656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21986, d206656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48101 q ha hb
    | true =>
      simp only [d21986, d206656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d21987 q = 1) (hb : d202307 q = 1) : d206657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21987, d206657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21987, d206657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d150161 q = 1) (hb : d202307 q = 1) : d206658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150161, d206658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150161, d206658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d150162 q = 1) (hb : d202307 q = 1) : d206659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150162, d206659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150162, d206659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d150163 q = 1) (hb : d202307 q = 1) : d206660 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150163, d206660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d150163, d206660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d150164 q = 1) (hb : d202307 q = 1) : d206661 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150164, d206661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150164, d206661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro48103 (p : Pattern) (ha : d150171 p = 1) (hb : d202307 p = 1) : d206686 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21980 q = 1) (hb : d202307 q = 1) : d206653 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21980, d206653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48099 q ha hb
    | true =>
      simp only [d21980, d206653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48100 q ha hb
  have h2 (q : Pattern) (ha : d150160 q = 1) (hb : d202307 q = 1) : d206654 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150160, d206654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150160, d206654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21986 q = 1) (hb : d202307 q = 1) : d206656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21986, d206656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48101 q ha hb
    | true =>
      simp only [d21986, d206656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21987 q = 1) (hb : d202307 q = 1) : d206657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21987, d206657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21987, d206657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150161 q = 1) (hb : d202307 q = 1) : d206658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150161, d206658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150161, d206658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150169 q = 1) (hb : d202307 q = 1) : d206684 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150169, d206684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150169, d206684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150170 q = 1) (hb : d202307 q = 1) : d206685 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150170, d206685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150170, d206685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150171 q = 1) (hb : d202307 q = 1) : d206686 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150171, d206686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150171, d206686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48104 (p : Pattern) (ha : d22042 p = 1) (hb : d202307 p = 1) : d206700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22024 q = 1) (hb : d202307 q = 1) : d206694 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22024, d206694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22024, d206694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48084 q ha hb
  have h2 (q : Pattern) (ha : d21835 q = 1) (hb : d202307 q = 1) : d206585 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21835, d206585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48084 q ha hb
    | true =>
      simp only [d21835, d206585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22025 q = 1) (hb : d202307 q = 1) : d206695 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22025, d206695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22025, d206695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21836 q = 1) (hb : d202307 q = 1) : d206586 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21836, d206586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21836, d206586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22026 q = 1) (hb : d202307 q = 1) : d206696 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22026, d206696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22026, d206696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22027 q = 1) (hb : d202307 q = 1) : d206697 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22027, d206697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22027, d206697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22028 q = 1) (hb : d202307 q = 1) : d206406 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22028, d206406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22028, d206406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48049 q ha hb
  have h8 (q : Pattern) (ha : d21737 q = 1) (hb : d202307 q = 1) : d206312 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21737, d206312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48049 q ha hb
    | true =>
      simp only [d21737, d206312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22029 q = 1) (hb : d202307 q = 1) : d206407 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22029, d206407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22029, d206407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21738 q = 1) (hb : d202307 q = 1) : d206313 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21738, d206313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21738, d206313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22030 q = 1) (hb : d202307 q = 1) : d206408 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22030, d206408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22030, d206408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22031 q = 1) (hb : d202307 q = 1) : d206409 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22031, d206409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22031, d206409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22032 q = 1) (hb : d202307 q = 1) : d206698 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22032, d206698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22032, d206698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22033 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48085 q ha hb
  have h15 (q : Pattern) (ha : d21841 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48085 q ha hb
    | true =>
      simp only [d21841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d22034 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21842 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d21842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d22035 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d22035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d22036 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d22036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d22037 q = 1) (hb : d202307 q = 1) : d206411 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22037, d206411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22037, d206411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48052 q ha hb
  have h21 (q : Pattern) (ha : d21748 q = 1) (hb : d202307 q = 1) : d206324 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21748, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48052 q ha hb
    | true =>
      simp only [d21748, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d22038 q = 1) (hb : d202307 q = 1) : d206412 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22038, d206412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d22038, d206412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d21749 q = 1) (hb : d202307 q = 1) : d206325 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21749, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d21749, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d22039 q = 1) (hb : d202307 q = 1) : d206413 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22039, d206413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d22039, d206413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d22040 q = 1) (hb : d202307 q = 1) : d206414 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22040, d206414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d22040, d206414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d22041 q = 1) (hb : d202307 q = 1) : d206699 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22041, d206699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d22041, d206699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d22042 q = 1) (hb : d202307 q = 1) : d206700 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22042, d206700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22042, d206700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro48105 (p : Pattern) (ha : d22049 p = 1) (hb : d202307 p = 1) : d206706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22028 q = 1) (hb : d202307 q = 1) : d206406 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22028, d206406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22028, d206406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48049 q ha hb
  have h2 (q : Pattern) (ha : d21737 q = 1) (hb : d202307 q = 1) : d206312 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21737, d206312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48049 q ha hb
    | true =>
      simp only [d21737, d206312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22029 q = 1) (hb : d202307 q = 1) : d206407 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22029, d206407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22029, d206407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21738 q = 1) (hb : d202307 q = 1) : d206313 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21738, d206313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21738, d206313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22030 q = 1) (hb : d202307 q = 1) : d206408 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22030, d206408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22030, d206408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22031 q = 1) (hb : d202307 q = 1) : d206409 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22031, d206409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22031, d206409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22043 q = 1) (hb : d202307 q = 1) : d206701 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22043, d206701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22043, d206701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48051 q ha hb
  have h8 (q : Pattern) (ha : d21742 q = 1) (hb : d202307 q = 1) : d206487 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d206487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48051 q ha hb
    | true =>
      simp only [d21742, d206487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22044 q = 1) (hb : d202307 q = 1) : d206702 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22044, d206702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22044, d206702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21743 q = 1) (hb : d202307 q = 1) : d206488 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d206488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21743, d206488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22045 q = 1) (hb : d202307 q = 1) : d206703 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22045, d206703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22045, d206703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22046 q = 1) (hb : d202307 q = 1) : d206704 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22046, d206704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22046, d206704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22047 q = 1) (hb : d202307 q = 1) : d206705 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22047, d206705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22047, d206705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22037 q = 1) (hb : d202307 q = 1) : d206411 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22037, d206411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22037, d206411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48052 q ha hb
  have h15 (q : Pattern) (ha : d21748 q = 1) (hb : d202307 q = 1) : d206324 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21748, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48052 q ha hb
    | true =>
      simp only [d21748, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d22038 q = 1) (hb : d202307 q = 1) : d206412 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22038, d206412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22038, d206412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21749 q = 1) (hb : d202307 q = 1) : d206325 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21749, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d21749, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d22039 q = 1) (hb : d202307 q = 1) : d206413 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22039, d206413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d22039, d206413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d22040 q = 1) (hb : d202307 q = 1) : d206414 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22040, d206414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d22040, d206414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d13164 q = 1) (hb : d202307 q = 1) : d206205 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13164, d206205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13164, d206205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48047 q ha hb
  have h21 (q : Pattern) (ha : d13025 q = 1) (hb : d202307 q = 1) : d206135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48047 q ha hb
    | true =>
      simp only [d13025, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d13165 q = 1) (hb : d202307 q = 1) : d206206 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13165, d206206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d13165, d206206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d13026 q = 1) (hb : d202307 q = 1) : d206136 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d13026, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d13166 q = 1) (hb : d202307 q = 1) : d206207 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13166, d206207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d13166, d206207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d13167 q = 1) (hb : d202307 q = 1) : d206208 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13167, d206208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13167, d206208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d22048 q = 1) (hb : d202307 q = 1) : d206415 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22048, d206415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d22048, d206415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d22049 q = 1) (hb : d202307 q = 1) : d206706 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22049, d206706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22049, d206706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro48106 (p : Pattern) (ha : d22059 p = 1) (hb : d202307 p = 1) : d206716 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22053 q = 1) (hb : d202307 q = 1) : d206710 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22053, d206710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22053, d206710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48087 q ha hb
  have h2 (q : Pattern) (ha : d21851 q = 1) (hb : d202307 q = 1) : d206601 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21851, d206601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48087 q ha hb
    | true =>
      simp only [d21851, d206601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22054 q = 1) (hb : d202307 q = 1) : d206711 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22054, d206711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22054, d206711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21852 q = 1) (hb : d202307 q = 1) : d206602 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21852, d206602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21852, d206602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22055 q = 1) (hb : d202307 q = 1) : d206712 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22055, d206712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22055, d206712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22056 q = 1) (hb : d202307 q = 1) : d206713 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22056, d206713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22056, d206713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13164 q = 1) (hb : d202307 q = 1) : d206205 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13164, d206205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13164, d206205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48047 q ha hb
  have h8 (q : Pattern) (ha : d13025 q = 1) (hb : d202307 q = 1) : d206135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48047 q ha hb
    | true =>
      simp only [d13025, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13165 q = 1) (hb : d202307 q = 1) : d206206 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13165, d206206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13165, d206206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13026 q = 1) (hb : d202307 q = 1) : d206136 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13026, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13166 q = 1) (hb : d202307 q = 1) : d206207 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13166, d206207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13166, d206207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13167 q = 1) (hb : d202307 q = 1) : d206208 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13167, d206208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13167, d206208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22057 q = 1) (hb : d202307 q = 1) : d206714 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22057, d206714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22057, d206714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22058 q = 1) (hb : d202307 q = 1) : d206715 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22058, d206715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22058, d206715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22059 q = 1) (hb : d202307 q = 1) : d206716 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22059, d206716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22059, d206716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48107 (p : Pattern) (ha : d22078 p = 1) (hb : d202307 p = 1) : d206735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22073 q = 1) (hb : d202307 q = 1) : d206730 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22073, d206730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22073, d206730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48057 q ha hb
  have h2 (q : Pattern) (ha : d21766 q = 1) (hb : d202307 q = 1) : d206513 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21766, d206513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48057 q ha hb
    | true =>
      simp only [d21766, d206513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22074 q = 1) (hb : d202307 q = 1) : d206731 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22074, d206731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22074, d206731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21767 q = 1) (hb : d202307 q = 1) : d206514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21767, d206514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21767, d206514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22075 q = 1) (hb : d202307 q = 1) : d206732 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22075, d206732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22075, d206732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22076 q = 1) (hb : d202307 q = 1) : d206733 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22076, d206733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22076, d206733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22077 q = 1) (hb : d202307 q = 1) : d206734 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22077, d206734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22077, d206734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15019 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48056 q ha hb
  have h9 (q : Pattern) (ha : d9844 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48056 q ha hb
    | true =>
      simp only [d9844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15020 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9846 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15021 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15022 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15023 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22078 q = 1) (hb : d202307 q = 1) : d206735 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22078, d206735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22078, d206735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48108 (p : Pattern) (ha : d22084 p = 1) (hb : d202307 p = 1) : d206741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22050 q = 1) (hb : d202307 q = 1) : d206707 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22050, d206707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48104 q ha hb
    | true =>
      simp only [d22050, d206707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48105 q ha hb
  have h2 (q : Pattern) (ha : d22051 q = 1) (hb : d202307 q = 1) : d206708 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22051, d206708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22051, d206708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22052 q = 1) (hb : d202307 q = 1) : d206709 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22052, d206709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22052, d206709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22060 q = 1) (hb : d202307 q = 1) : d206717 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22060, d206717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48105 q ha hb
    | true =>
      simp only [d22060, d206717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48106 q ha hb
  have h5 (q : Pattern) (ha : d22061 q = 1) (hb : d202307 q = 1) : d206718 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22061, d206718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22061, d206718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22062 q = 1) (hb : d202307 q = 1) : d206719 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22062, d206719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22062, d206719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22063 q = 1) (hb : d202307 q = 1) : d206720 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22063, d206720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22063, d206720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22070 q = 1) (hb : d202307 q = 1) : d206727 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d206727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48105 q ha hb
    | true =>
      simp only [d22070, d206727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48073 q ha hb
  have h9 (q : Pattern) (ha : d22071 q = 1) (hb : d202307 q = 1) : d206728 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d206728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d206728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22072 q = 1) (hb : d202307 q = 1) : d206729 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d206729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d206729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22079 q = 1) (hb : d202307 q = 1) : d206736 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22079, d206736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48073 q ha hb
    | true =>
      simp only [d22079, d206736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48107 q ha hb
  have h12 (q : Pattern) (ha : d22080 q = 1) (hb : d202307 q = 1) : d206737 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22080, d206737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22080, d206737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22081 q = 1) (hb : d202307 q = 1) : d206738 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22081, d206738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22081, d206738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22082 q = 1) (hb : d202307 q = 1) : d206739 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d206739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22082, d206739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22083 q = 1) (hb : d202307 q = 1) : d206740 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22083, d206740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22083, d206740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22084 q = 1) (hb : d202307 q = 1) : d206741 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22084, d206741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d22084, d206741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro48109 (p : Pattern) (ha : d22089 p = 1) (hb : d202307 p = 1) : d206746 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22070 q = 1) (hb : d202307 q = 1) : d206727 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d206727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48105 q ha hb
    | true =>
      simp only [d22070, d206727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48073 q ha hb
  have h2 (q : Pattern) (ha : d22071 q = 1) (hb : d202307 q = 1) : d206728 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d206728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d206728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22072 q = 1) (hb : d202307 q = 1) : d206729 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d206729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d206729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22079 q = 1) (hb : d202307 q = 1) : d206736 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22079, d206736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48073 q ha hb
    | true =>
      simp only [d22079, d206736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48107 q ha hb
  have h5 (q : Pattern) (ha : d22080 q = 1) (hb : d202307 q = 1) : d206737 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22080, d206737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22080, d206737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22081 q = 1) (hb : d202307 q = 1) : d206738 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22081, d206738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22081, d206738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22082 q = 1) (hb : d202307 q = 1) : d206739 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d206739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22082, d206739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22087 q = 1) (hb : d202307 q = 1) : d206744 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22087, d206744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22087, d206744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22088 q = 1) (hb : d202307 q = 1) : d206745 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22088, d206745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22088, d206745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22089 q = 1) (hb : d202307 q = 1) : d206746 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22089, d206746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22089, d206746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro48110 (p : Pattern) (ha : d22095 p = 1) (hb : d202307 p = 1) : d206752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22085 q = 1) (hb : d202307 q = 1) : d206742 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22085, d206742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48108 q ha hb
    | true =>
      simp only [d22085, d206742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22086 q = 1) (hb : d202307 q = 1) : d206743 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22086, d206743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22086, d206743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22090 q = 1) (hb : d202307 q = 1) : d206747 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22090, d206747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48109 q ha hb
    | true =>
      simp only [d22090, d206747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22091 q = 1) (hb : d202307 q = 1) : d206748 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22091, d206748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22091, d206748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22092 q = 1) (hb : d202307 q = 1) : d206749 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22092, d206749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22092, d206749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22093 q = 1) (hb : d202307 q = 1) : d206750 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22093, d206750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22093, d206750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22094 q = 1) (hb : d202307 q = 1) : d206751 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22094, d206751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22094, d206751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22095 q = 1) (hb : d202307 q = 1) : d206752 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22095, d206752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22095, d206752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48111 (p : Pattern) (ha : d22109 p = 1) (hb : d202307 p = 1) : d206766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22090 q = 1) (hb : d202307 q = 1) : d206747 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22090, d206747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48109 q ha hb
    | true =>
      simp only [d22090, d206747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22091 q = 1) (hb : d202307 q = 1) : d206748 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22091, d206748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22091, d206748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22104 q = 1) (hb : d202307 q = 1) : d206761 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22104, d206761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48075 q ha hb
    | true =>
      simp only [d22104, d206761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22105 q = 1) (hb : d202307 q = 1) : d206762 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22105, d206762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22105, d206762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22106 q = 1) (hb : d202307 q = 1) : d206763 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22106, d206763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22106, d206763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22107 q = 1) (hb : d202307 q = 1) : d206764 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22107, d206764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22107, d206764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22108 q = 1) (hb : d202307 q = 1) : d206765 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22108, d206765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22108, d206765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22109 q = 1) (hb : d202307 q = 1) : d206766 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22109, d206766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22109, d206766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48112 (p : Pattern) (ha : d22174 p = 1) (hb : d202307 p = 1) : d206754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22064 q = 1) (hb : d202307 q = 1) : d206721 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22064, d206721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22064, d206721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48054 q ha hb
  have h2 (q : Pattern) (ha : d21755 q = 1) (hb : d202307 q = 1) : d206497 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d206497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48054 q ha hb
    | true =>
      simp only [d21755, d206497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22065 q = 1) (hb : d202307 q = 1) : d206722 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22065, d206722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22065, d206722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21756 q = 1) (hb : d202307 q = 1) : d206498 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d206498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21756, d206498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22066 q = 1) (hb : d202307 q = 1) : d206723 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22066, d206723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22066, d206723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22067 q = 1) (hb : d202307 q = 1) : d206724 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22067, d206724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22067, d206724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22096 q = 1) (hb : d202307 q = 1) : d206753 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22096, d206753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22096, d206753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22174 q = 1) (hb : d202307 q = 1) : d206754 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22174, d206754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22174, d206754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48113 (p : Pattern) (ha : d22180 p = 1) (hb : d202307 p = 1) : d206770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22070 q = 1) (hb : d202307 q = 1) : d206727 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d206727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48105 q ha hb
    | true =>
      simp only [d22070, d206727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48073 q ha hb
  have h2 (q : Pattern) (ha : d22071 q = 1) (hb : d202307 q = 1) : d206728 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d206728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d206728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22072 q = 1) (hb : d202307 q = 1) : d206729 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d206729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d206729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22079 q = 1) (hb : d202307 q = 1) : d206736 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22079, d206736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48073 q ha hb
    | true =>
      simp only [d22079, d206736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48107 q ha hb
  have h5 (q : Pattern) (ha : d22080 q = 1) (hb : d202307 q = 1) : d206737 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22080, d206737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22080, d206737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22081 q = 1) (hb : d202307 q = 1) : d206738 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22081, d206738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22081, d206738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22082 q = 1) (hb : d202307 q = 1) : d206739 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d206739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22082, d206739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22175 q = 1) (hb : d202307 q = 1) : d206755 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22175, d206755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48073 q ha hb
    | true =>
      simp only [d22175, d206755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48112 q ha hb
  have h9 (q : Pattern) (ha : d22176 q = 1) (hb : d202307 q = 1) : d206756 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22176, d206756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22176, d206756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22177 q = 1) (hb : d202307 q = 1) : d206757 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22177, d206757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22177, d206757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22178 q = 1) (hb : d202307 q = 1) : d206758 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22178, d206758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22178, d206758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d22179 q = 1) (hb : d202307 q = 1) : d206769 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22179, d206769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22179, d206769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22180 q = 1) (hb : d202307 q = 1) : d206770 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22180, d206770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22180, d206770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro48114 (p : Pattern) (ha : d22186 p = 1) (hb : d202307 p = 1) : d206776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22181 q = 1) (hb : d202307 q = 1) : d206771 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22181, d206771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48113 q ha hb
    | true =>
      simp only [d22181, d206771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22182 q = 1) (hb : d202307 q = 1) : d206772 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22182, d206772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22182, d206772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22183 q = 1) (hb : d202307 q = 1) : d206773 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22183, d206773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22183, d206773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22184 q = 1) (hb : d202307 q = 1) : d206774 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22184, d206774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22184, d206774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22185 q = 1) (hb : d202307 q = 1) : d206775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22185, d206775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22185, d206775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22186 q = 1) (hb : d202307 q = 1) : d206776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22186, d206776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22186, d206776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48115 (p : Pattern) (ha : d150181 p = 1) (hb : d202307 p = 1) : d206782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22110 q = 1) (hb : d202307 q = 1) : d206767 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22110, d206767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48110 q ha hb
    | true =>
      simp only [d22110, d206767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48111 q ha hb
  have h2 (q : Pattern) (ha : d150177 q = 1) (hb : d202307 q = 1) : d206768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150177, d206768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150177, d206768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22187 q = 1) (hb : d202307 q = 1) : d206777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22187, d206777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48114 q ha hb
    | true =>
      simp only [d22187, d206777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22188 q = 1) (hb : d202307 q = 1) : d206778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22188, d206778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22188, d206778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150178 q = 1) (hb : d202307 q = 1) : d206779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150178, d206779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150178, d206779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150179 q = 1) (hb : d202307 q = 1) : d206780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150179, d206780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150179, d206780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150180 q = 1) (hb : d202307 q = 1) : d206781 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150180, d206781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150180, d206781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150181 q = 1) (hb : d202307 q = 1) : d206782 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150181, d206782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150181, d206782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48116 (p : Pattern) (ha : d150187 p = 1) (hb : d202307 p = 1) : d206799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21804 q = 1) (hb : d202307 q = 1) : d206551 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21804, d206551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21804, d206551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48064 q ha hb
  have h2 (q : Pattern) (ha : d21805 q = 1) (hb : d202307 q = 1) : d206552 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21805, d206552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21805, d206552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21814 q = 1) (hb : d202307 q = 1) : d206561 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21814, d206561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48064 q ha hb
    | true =>
      simp only [d21814, d206561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48067 q ha hb
  have h4 (q : Pattern) (ha : d21815 q = 1) (hb : d202307 q = 1) : d206562 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21815, d206562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21815, d206562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21816 q = 1) (hb : d202307 q = 1) : d206563 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d21816, d206563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21816, d206563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150165 q = 1) (hb : d202307 q = 1) : d206662 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150165, d206662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48094 q ha hb
    | true =>
      simp only [d150165, d206662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48102 q ha hb
  have h7 (q : Pattern) (ha : d22010 q = 1) (hb : d202307 q = 1) : d206680 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22010, d206680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48070 q ha hb
    | true =>
      simp only [d22010, d206680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48071 q ha hb
  have h8 (q : Pattern) (ha : d150166 q = 1) (hb : d202307 q = 1) : d206681 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150166, d206681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150166, d206681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150167 q = 1) (hb : d202307 q = 1) : d206682 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150167, d206682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150167, d206682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d150168 q = 1) (hb : d202307 q = 1) : d206683 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150168, d206683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150168, d206683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150172 q = 1) (hb : d202307 q = 1) : d206687 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150172, d206687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150172, d206687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48103 q ha hb
  have h12 (q : Pattern) (ha : d22019 q = 1) (hb : d202307 q = 1) : d206689 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22019, d206689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22019, d206689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48072 q ha hb
  have h13 (q : Pattern) (ha : d150173 q = 1) (hb : d202307 q = 1) : d206690 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150173, d206690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150173, d206690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150174 q = 1) (hb : d202307 q = 1) : d206691 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150174, d206691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150174, d206691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150175 q = 1) (hb : d202307 q = 1) : d206692 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150175, d206692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150175, d206692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d150176 q = 1) (hb : d202307 q = 1) : d206693 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150176, d206693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150176, d206693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150182 q = 1) (hb : d202307 q = 1) : d206783 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150182, d206783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150182, d206783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48115 q ha hb
  have h18 (q : Pattern) (ha : d22204 q = 1) (hb : d202307 q = 1) : d206794 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22204, d206794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22204, d206794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48077 q ha hb
  have h19 (q : Pattern) (ha : d150183 q = 1) (hb : d202307 q = 1) : d206795 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150183, d206795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150183, d206795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d150184 q = 1) (hb : d202307 q = 1) : d206796 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150184, d206796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150184, d206796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d150185 q = 1) (hb : d202307 q = 1) : d206797 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150185, d206797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150185, d206797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d150186 q = 1) (hb : d202307 q = 1) : d206798 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150186, d206798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150186, d206798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d150187 q = 1) (hb : d202307 q = 1) : d206799 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150187, d206799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150187, d206799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro48117 (p : Pattern) (ha : d150193 p = 1) (hb : d202307 p = 1) : d206805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150188 q = 1) (hb : d202307 q = 1) : d206800 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150188, d206800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150188, d206800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48116 q ha hb
  have h2 (q : Pattern) (ha : d150189 q = 1) (hb : d202307 q = 1) : d206801 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150189, d206801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150189, d206801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150190 q = 1) (hb : d202307 q = 1) : d206802 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150190, d206802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150190, d206802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150191 q = 1) (hb : d202307 q = 1) : d206803 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150191, d206803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150191, d206803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150192 q = 1) (hb : d202307 q = 1) : d206804 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150192, d206804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150192, d206804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150193 q = 1) (hb : d202307 q = 1) : d206805 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150193, d206805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150193, d206805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48118 (p : Pattern) (ha : d1522 p = 1) (hb : d202304 p = 1) : d31302 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d820 q = 1) : d820 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1521 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1522 q = 1) (hb : d202304 q = 1) : d31302 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d1522, d202304, d31302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1522, d202304, d31302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48119 (p : Pattern) (ha : d1526 p = 1) (hb : d202304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1525 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1526 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d1526, d202304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1526, d202304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48120 (p : Pattern) (ha : d1533 p = 1) (hb : d202304 p = 1) : d28879 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d826 q = 1) : d826 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1532 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1533 q = 1) (hb : d202304 q = 1) : d28879 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d1533, d202304, d28879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1533, d202304, d28879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48121 (p : Pattern) (ha : d10035 p = 1) (hb : d202307 p = 1) : d206584 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1201 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1527 q = 1) (hb : d202304 q = 1) : d31303 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d31303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48118 q ha hb
    | true =>
      simp only [d1527, d31303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48119 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1528 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48048 q ha hb
  have h4 (q : Pattern) (ha : d1529 q = 1) (hb : d202304 q = 1) : d31304 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d31304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1529, d31304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1530 q = 1) (hb : d202306 q = 1) : d31736 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1530, d202306, d31736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1530, d202306, d31736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1205 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1534 q = 1) (hb : d202304 q = 1) : d28880 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1534, d28880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48120 q ha hb
    | true =>
      simp only [d1534, d28880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d1535 q = 1) (hb : d202304 q = 1) : d28881 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1535, d28881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1535, d28881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d1536 q = 1) (hb : d202306 q = 1) : d206581 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1536, d202306, d206581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1536, d202306, d206581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1537 q = 1) (hb : d202306 q = 1) : d206582 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1537, d206582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1537, d206582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d1538 q = 1) (hb : d202306 q = 1) : d206583 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1538, d206583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1538, d206583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10035 q = 1) (hb : d202307 q = 1) : d206584 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10035, d202307, d206584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10035, d202307, d206584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro48122 (p : Pattern) (ha : d5122 p = 1) (hb : d202304 p = 1) : d206317 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d5121 q = 1) : d5121 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1547 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5122 q = 1) (hb : d202304 q = 1) : d206317 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d5122, d202304, d206317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5122, d202304, d206317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48123 (p : Pattern) (ha : d13350 p = 1) (hb : d202307 p = 1) : d206323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1545 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10057 q = 1) (hb : d202304 q = 1) : d206318 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10057, d206318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48122 q ha hb
    | true =>
      simp only [d10057, d206318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10058 q = 1) (hb : d202304 q = 1) : d206319 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10058, d206319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10058, d206319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d10080 q = 1) (hb : d202306 q = 1) : d206320 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10080, d202306, d206320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10080, d202306, d206320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1550 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10081 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10081, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d10081, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10082 q = 1) (hb : d202306 q = 1) : d206321 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10082, d206321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10082, d206321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10083 q = 1) (hb : d202306 q = 1) : d206322 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10083, d206322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10083, d206322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13350 q = 1) (hb : d202307 q = 1) : d206323 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13350, d202307, d206323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13350, d202307, d206323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48124 (p : Pattern) (ha : d1539 p = 1) (hb : d202304 p = 1) : d32140 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1521 q = 1) : d1521 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1532 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1539 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d1539, d202304, d32140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1539, d202304, d32140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48125 (p : Pattern) (ha : d1542 p = 1) (hb : d202304 p = 1) : d32153 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1525 q = 1) : d1525 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1541 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1542 q = 1) (hb : d202304 q = 1) : d32153 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d1542, d202304, d32153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1542, d202304, d32153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48126 (p : Pattern) (ha : d1548 p = 1) (hb : d202304 p = 1) : d25764 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1532 q = 1) : d1532 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1547 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1548 q = 1) (hb : d202304 q = 1) : d25764 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d1548, d202304, d25764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1548, d202304, d25764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48127 (p : Pattern) (ha : d22219 p = 1) (hb : d202307 p = 1) : d206812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1529 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1543 q = 1) (hb : d202304 q = 1) : d32154 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d32154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48124 q ha hb
    | true =>
      simp only [d1543, d32154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48125 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1544 q = 1) (hb : d202304 q = 1) : d32155 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1544, d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48050 q ha hb
  have h4 (q : Pattern) (ha : d1545 q = 1) (hb : d202304 q = 1) : d32156 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d32156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1545, d32156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1546 q = 1) (hb : d202306 q = 1) : d206809 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1546, d202306, d206809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1546, d202306, d206809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1535 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1549 q = 1) (hb : d202304 q = 1) : d25765 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1549, d25765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48126 q ha hb
    | true =>
      simp only [d1549, d25765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d1550 q = 1) (hb : d202304 q = 1) : d25766 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1550, d25766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1550, d25766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d1551 q = 1) (hb : d202306 q = 1) : d31739 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1551, d202306, d31739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1551, d202306, d31739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1552 q = 1) (hb : d202306 q = 1) : d206810 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1552, d206810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1552, d206810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d1553 q = 1) (hb : d202306 q = 1) : d206811 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1553, d206811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1553, d206811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d22219 q = 1) (hb : d202307 q = 1) : d206812 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22219, d202307, d206812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22219, d202307, d206812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro48128 (p : Pattern) (ha : d22225 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1529 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10051 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10051, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10051, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10052 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10053 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d22225 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22225, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22225, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro48129 (p : Pattern) (ha : d22231 p = 1) (hb : d202307 p = 1) : d206818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10036 q = 1) (hb : d202307 q = 1) : d206585 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d206585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48121 q ha hb
    | true =>
      simp only [d10036, d206585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10038 q = 1) (hb : d202307 q = 1) : d206586 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d206586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10038, d206586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16859 q = 1) (hb : d202307 q = 1) : d206587 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16859, d206587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16859, d206587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16860 q = 1) (hb : d202307 q = 1) : d206588 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16860, d206588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16860, d206588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22220 q = 1) (hb : d202307 q = 1) : d206813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d206813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48127 q ha hb
    | true =>
      simp only [d22220, d206813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22221 q = 1) (hb : d202307 q = 1) : d206814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d206814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22221, d206814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22222 q = 1) (hb : d202307 q = 1) : d206815 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22222, d206815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22222, d206815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22223 q = 1) (hb : d202307 q = 1) : d206816 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22223, d206816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22223, d206816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22224 q = 1) (hb : d202307 q = 1) : d206817 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22224, d206817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22224, d206817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22226 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48128 q ha hb
    | true =>
      simp only [d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22227 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d22228 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22229 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d13351 q = 1) (hb : d202307 q = 1) : d206324 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48123 q ha hb
    | true =>
      simp only [d13351, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d13352 q = 1) (hb : d202307 q = 1) : d206325 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d13352, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d13353 q = 1) (hb : d202307 q = 1) : d206326 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13353, d206326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13353, d206326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13354 q = 1) (hb : d202307 q = 1) : d206327 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13354, d206327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13354, d206327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d22230 q = 1) (hb : d202307 q = 1) : d206590 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22230, d206590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22230, d206590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d22231 q = 1) (hb : d202307 q = 1) : d206818 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22231, d206818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22231, d206818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro48130 (p : Pattern) (ha : d22232 p = 1) (hb : d202307 p = 1) : d206824 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1545 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1559 q = 1) (hb : d202304 q = 1) : d1559 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1560 q = 1) (hb : d202304 q = 1) : d206819 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1560, d206819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48126 q ha hb
    | true =>
      simp only [d1560, d206819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1115 q = 1) (hb : d202304 q = 1) : d1115 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1561 q = 1) (hb : d202304 q = 1) : d206820 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1561, d206820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1561, d206820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1562 q = 1) (hb : d202306 q = 1) : d206821 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1562, d202306, d206821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1562, d202306, d206821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1550 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1565 q = 1) (hb : d202304 q = 1) : d1565 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1566 q = 1) (hb : d202306 q = 1) : d29564 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1566, d202306, d29564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1566, d202306, d29564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1567 q = 1) (hb : d202306 q = 1) : d206822 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1567, d206822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1567, d206822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1568 q = 1) (hb : d202306 q = 1) : d206823 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1568, d206823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1568, d206823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22232 q = 1) (hb : d202307 q = 1) : d206824 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22232, d202307, d206824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22232, d202307, d206824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro48131 (p : Pattern) (ha : d22239 p = 1) (hb : d202307 p = 1) : d206831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22220 q = 1) (hb : d202307 q = 1) : d206813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d206813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48127 q ha hb
    | true =>
      simp only [d22220, d206813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22221 q = 1) (hb : d202307 q = 1) : d206814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d206814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22221, d206814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22222 q = 1) (hb : d202307 q = 1) : d206815 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22222, d206815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22222, d206815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22223 q = 1) (hb : d202307 q = 1) : d206816 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22223, d206816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22223, d206816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22233 q = 1) (hb : d202307 q = 1) : d206825 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d206825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48130 q ha hb
    | true =>
      simp only [d22233, d206825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22234 q = 1) (hb : d202307 q = 1) : d206826 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d206826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22234, d206826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22235 q = 1) (hb : d202307 q = 1) : d206827 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22235, d206827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22235, d206827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22236 q = 1) (hb : d202307 q = 1) : d206828 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22236, d206828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22236, d206828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22237 q = 1) (hb : d202307 q = 1) : d206829 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22237, d206829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22237, d206829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13351 q = 1) (hb : d202307 q = 1) : d206324 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48123 q ha hb
    | true =>
      simp only [d13351, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13352 q = 1) (hb : d202307 q = 1) : d206325 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13352, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13353 q = 1) (hb : d202307 q = 1) : d206326 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13353, d206326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13353, d206326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13354 q = 1) (hb : d202307 q = 1) : d206327 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13354, d206327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13354, d206327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d22238 q = 1) (hb : d202307 q = 1) : d206830 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22238, d206830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22238, d206830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22239 q = 1) (hb : d202307 q = 1) : d206831 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22239, d206831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22239, d206831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48132 (p : Pattern) (ha : d10134 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1576 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1593 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1593, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1593, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10130 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10131 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10131, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d10131, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d10132 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10133 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10134 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10134, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10134, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro48133 (p : Pattern) (ha : d22243 p = 1) (hb : d202307 p = 1) : d206840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1545 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1563 q = 1) (hb : d202304 q = 1) : d1563 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5123 q = 1) (hb : d202304 q = 1) : d206835 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5123, d206835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48122 q ha hb
    | true =>
      simp only [d5123, d206835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5124 q = 1) (hb : d202304 q = 1) : d206836 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5124, d206836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5124, d206836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5125 q = 1) (hb : d202306 q = 1) : d206837 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5125, d202306, d206837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5125, d202306, d206837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1550 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1565 q = 1) (hb : d202304 q = 1) : d1565 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1566 q = 1) (hb : d202306 q = 1) : d29564 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1566, d202306, d29564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1566, d202306, d29564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5126 q = 1) (hb : d202306 q = 1) : d206838 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5126, d206838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5126, d206838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5127 q = 1) (hb : d202306 q = 1) : d206839 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5127, d206839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5127, d206839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22243 q = 1) (hb : d202307 q = 1) : d206840 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22243, d202307, d206840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22243, d202307, d206840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro48134 (p : Pattern) (ha : d22249 p = 1) (hb : d202307 p = 1) : d206846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22244 q = 1) (hb : d202307 q = 1) : d206841 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22244, d206841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48133 q ha hb
    | true =>
      simp only [d22244, d206841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22245 q = 1) (hb : d202307 q = 1) : d206842 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22245, d206842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22245, d206842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22246 q = 1) (hb : d202307 q = 1) : d206843 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22246, d206843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22246, d206843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22247 q = 1) (hb : d202307 q = 1) : d206844 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22247, d206844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22247, d206844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22248 q = 1) (hb : d202307 q = 1) : d206845 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22248, d206845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22248, d206845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10135 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48132 q ha hb
    | true =>
      simp only [d10135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10137 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15163 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15164 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15165 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22249 q = 1) (hb : d202307 q = 1) : d206846 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22249, d206846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22249, d206846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48135 (p : Pattern) (ha : d22255 p = 1) (hb : d202307 p = 1) : d206852 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22233 q = 1) (hb : d202307 q = 1) : d206825 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d206825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48130 q ha hb
    | true =>
      simp only [d22233, d206825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22234 q = 1) (hb : d202307 q = 1) : d206826 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d206826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22234, d206826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22235 q = 1) (hb : d202307 q = 1) : d206827 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22235, d206827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22235, d206827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22236 q = 1) (hb : d202307 q = 1) : d206828 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22236, d206828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22236, d206828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22254 q = 1) (hb : d202307 q = 1) : d206851 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22254, d206851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22254, d206851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10135 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48132 q ha hb
    | true =>
      simp only [d10135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10137 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15163 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15164 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15165 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22255 q = 1) (hb : d202307 q = 1) : d206852 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22255, d206852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22255, d206852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48136 (p : Pattern) (ha : d22261 p = 1) (hb : d202307 p = 1) : d206858 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22240 q = 1) (hb : d202307 q = 1) : d206832 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22240, d206832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48129 q ha hb
    | true =>
      simp only [d22240, d206832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48131 q ha hb
  have h2 (q : Pattern) (ha : d22241 q = 1) (hb : d202307 q = 1) : d206833 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22241, d206833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22241, d206833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22242 q = 1) (hb : d202307 q = 1) : d206834 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22242, d206834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22242, d206834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22250 q = 1) (hb : d202307 q = 1) : d206847 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22250, d206847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48131 q ha hb
    | true =>
      simp only [d22250, d206847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48134 q ha hb
  have h5 (q : Pattern) (ha : d22251 q = 1) (hb : d202307 q = 1) : d206848 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22251, d206848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22251, d206848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22252 q = 1) (hb : d202307 q = 1) : d206849 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22252, d206849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22252, d206849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22253 q = 1) (hb : d202307 q = 1) : d206850 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22253, d206850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22253, d206850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22256 q = 1) (hb : d202307 q = 1) : d206853 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22256, d206853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48131 q ha hb
    | true =>
      simp only [d22256, d206853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48135 q ha hb
  have h9 (q : Pattern) (ha : d22257 q = 1) (hb : d202307 q = 1) : d206854 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22257, d206854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22257, d206854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22258 q = 1) (hb : d202307 q = 1) : d206855 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22258, d206855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22258, d206855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22259 q = 1) (hb : d202307 q = 1) : d206856 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22259, d206856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22259, d206856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d22260 q = 1) (hb : d202307 q = 1) : d206857 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22260, d206857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22260, d206857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22261 q = 1) (hb : d202307 q = 1) : d206858 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22261, d206858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22261, d206858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro48137 (p : Pattern) (ha : d22265 p = 1) (hb : d202307 p = 1) : d206862 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22256 q = 1) (hb : d202307 q = 1) : d206853 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22256, d206853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48131 q ha hb
    | true =>
      simp only [d22256, d206853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48135 q ha hb
  have h2 (q : Pattern) (ha : d22257 q = 1) (hb : d202307 q = 1) : d206854 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22257, d206854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22257, d206854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22258 q = 1) (hb : d202307 q = 1) : d206855 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22258, d206855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22258, d206855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22259 q = 1) (hb : d202307 q = 1) : d206856 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22259, d206856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22259, d206856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22264 q = 1) (hb : d202307 q = 1) : d206861 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22264, d206861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22264, d206861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22265 q = 1) (hb : d202307 q = 1) : d206862 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22265, d206862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22265, d206862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48138 (p : Pattern) (ha : d22271 p = 1) (hb : d202307 p = 1) : d206868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d202307 q = 1) : d206859 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d206859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48136 q ha hb
    | true =>
      simp only [d22262, d206859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d202307 q = 1) : d206860 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d206860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d206860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d202307 q = 1) : d206863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48137 q ha hb
    | true =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d202307 q = 1) : d206864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d202307 q = 1) : d206865 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d206865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d206865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22269 q = 1) (hb : d202307 q = 1) : d206866 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22269, d206866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22269, d206866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22270 q = 1) (hb : d202307 q = 1) : d206867 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22270, d206867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22270, d206867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22271 q = 1) (hb : d202307 q = 1) : d206868 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22271, d206868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22271, d206868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48139 (p : Pattern) (ha : d22275 p = 1) (hb : d202307 p = 1) : d206872 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d202307 q = 1) : d206863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48137 q ha hb
    | true =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d202307 q = 1) : d206864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d202307 q = 1) : d206869 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d206869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d206869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22273 q = 1) (hb : d202307 q = 1) : d206870 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22273, d206870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22273, d206870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22274 q = 1) (hb : d202307 q = 1) : d206871 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22274, d206871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22274, d206871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22275 q = 1) (hb : d202307 q = 1) : d206872 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22275, d206872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22275, d206872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48140 (p : Pattern) (ha : d22281 p = 1) (hb : d202307 p = 1) : d206878 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22276 q = 1) (hb : d202307 q = 1) : d206873 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22276, d206873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48138 q ha hb
    | true =>
      simp only [d22276, d206873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48139 q ha hb
  have h2 (q : Pattern) (ha : d22277 q = 1) (hb : d202307 q = 1) : d206874 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22277, d206874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22277, d206874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22278 q = 1) (hb : d202307 q = 1) : d206875 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22278, d206875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22278, d206875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22279 q = 1) (hb : d202307 q = 1) : d206876 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22279, d206876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22279, d206876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22280 q = 1) (hb : d202307 q = 1) : d206877 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22280, d206877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22280, d206877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22281 q = 1) (hb : d202307 q = 1) : d206878 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22281, d206878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22281, d206878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48141 (p : Pattern) (ha : d22284 p = 1) (hb : d202307 p = 1) : d206881 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d202307 q = 1) : d206859 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d206859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48136 q ha hb
    | true =>
      simp only [d22262, d206859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d202307 q = 1) : d206860 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d206860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d206860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d202307 q = 1) : d206863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48137 q ha hb
    | true =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d202307 q = 1) : d206864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d202307 q = 1) : d206865 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d206865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d206865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22269 q = 1) (hb : d202307 q = 1) : d206866 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22269, d206866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22269, d206866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22270 q = 1) (hb : d202307 q = 1) : d206867 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22270, d206867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22270, d206867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22284 q = 1) (hb : d202307 q = 1) : d206881 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22284, d206881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22284, d206881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48142 (p : Pattern) (ha : d22285 p = 1) (hb : d202307 p = 1) : d206882 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d202307 q = 1) : d206863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48137 q ha hb
    | true =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d202307 q = 1) : d206864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d202307 q = 1) : d206869 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d206869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d206869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22273 q = 1) (hb : d202307 q = 1) : d206870 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22273, d206870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22273, d206870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22274 q = 1) (hb : d202307 q = 1) : d206871 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22274, d206871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22274, d206871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22285 q = 1) (hb : d202307 q = 1) : d206882 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22285, d206882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22285, d206882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48143 (p : Pattern) (ha : d22291 p = 1) (hb : d202307 p = 1) : d206888 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22276 q = 1) (hb : d202307 q = 1) : d206873 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22276, d206873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48138 q ha hb
    | true =>
      simp only [d22276, d206873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48139 q ha hb
  have h2 (q : Pattern) (ha : d22277 q = 1) (hb : d202307 q = 1) : d206874 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22277, d206874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22277, d206874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22278 q = 1) (hb : d202307 q = 1) : d206875 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22278, d206875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22278, d206875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22279 q = 1) (hb : d202307 q = 1) : d206876 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22279, d206876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22279, d206876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22280 q = 1) (hb : d202307 q = 1) : d206877 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22280, d206877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22280, d206877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22286 q = 1) (hb : d202307 q = 1) : d206883 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22286, d206883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48141 q ha hb
    | true =>
      simp only [d22286, d206883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48142 q ha hb
  have h7 (q : Pattern) (ha : d22287 q = 1) (hb : d202307 q = 1) : d206884 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22287, d206884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22287, d206884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22288 q = 1) (hb : d202307 q = 1) : d206885 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22288, d206885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22288, d206885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22289 q = 1) (hb : d202307 q = 1) : d206886 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22289, d206886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22289, d206886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22290 q = 1) (hb : d202307 q = 1) : d206887 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22290, d206887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22290, d206887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22291 q = 1) (hb : d202307 q = 1) : d206888 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22291, d206888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22291, d206888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48144 (p : Pattern) (ha : d22340 p = 1) (hb : d202307 p = 1) : d206934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22240 q = 1) (hb : d202307 q = 1) : d206832 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22240, d206832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48129 q ha hb
    | true =>
      simp only [d22240, d206832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48131 q ha hb
  have h2 (q : Pattern) (ha : d22241 q = 1) (hb : d202307 q = 1) : d206833 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22241, d206833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22241, d206833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22242 q = 1) (hb : d202307 q = 1) : d206834 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22242, d206834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22242, d206834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22250 q = 1) (hb : d202307 q = 1) : d206847 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22250, d206847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48131 q ha hb
    | true =>
      simp only [d22250, d206847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48134 q ha hb
  have h5 (q : Pattern) (ha : d22251 q = 1) (hb : d202307 q = 1) : d206848 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22251, d206848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22251, d206848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22252 q = 1) (hb : d202307 q = 1) : d206849 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22252, d206849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22252, d206849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22253 q = 1) (hb : d202307 q = 1) : d206850 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22253, d206850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22253, d206850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22338 q = 1) (hb : d202307 q = 1) : d206932 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22338, d206932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22338, d206932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22339 q = 1) (hb : d202307 q = 1) : d206933 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22339, d206933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22339, d206933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22340 q = 1) (hb : d202307 q = 1) : d206934 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22340, d206934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22340, d206934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro48145 (p : Pattern) (ha : d22350 p = 1) (hb : d202307 p = 1) : d206944 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22341 q = 1) (hb : d202307 q = 1) : d206935 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22341, d206935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48144 q ha hb
    | true =>
      simp only [d22341, d206935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22342 q = 1) (hb : d202307 q = 1) : d206936 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22342, d206936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22342, d206936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d202307 q = 1) : d206863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48137 q ha hb
    | true =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d202307 q = 1) : d206864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22347 q = 1) (hb : d202307 q = 1) : d206941 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22347, d206941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22347, d206941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22348 q = 1) (hb : d202307 q = 1) : d206942 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22348, d206942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22348, d206942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22349 q = 1) (hb : d202307 q = 1) : d206943 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22349, d206943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22349, d206943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22350 q = 1) (hb : d202307 q = 1) : d206944 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22350, d206944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22350, d206944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48146 (p : Pattern) (ha : d22476 p = 1) (hb : d202307 p = 1) : d206990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22466 q = 1) (hb : d202307 q = 1) : d206980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22466, d206980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48145 q ha hb
    | true =>
      simp only [d22466, d206980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48139 q ha hb
  have h2 (q : Pattern) (ha : d22467 q = 1) (hb : d202307 q = 1) : d206981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22467, d206981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22467, d206981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22468 q = 1) (hb : d202307 q = 1) : d206982 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22468, d206982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22468, d206982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22469 q = 1) (hb : d202307 q = 1) : d206983 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22469, d206983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22469, d206983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22470 q = 1) (hb : d202307 q = 1) : d206984 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22470, d206984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22470, d206984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22471 q = 1) (hb : d202307 q = 1) : d206985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22471, d206985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48139 q ha hb
    | true =>
      simp only [d22471, d206985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22472 q = 1) (hb : d202307 q = 1) : d206986 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22472, d206986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22472, d206986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22473 q = 1) (hb : d202307 q = 1) : d206987 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22473, d206987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22473, d206987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22474 q = 1) (hb : d202307 q = 1) : d206988 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22474, d206988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22474, d206988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22475 q = 1) (hb : d202307 q = 1) : d206989 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22475, d206989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22475, d206989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22476 q = 1) (hb : d202307 q = 1) : d206990 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22476, d206990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22476, d206990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48147 (p : Pattern) (ha : d22482 p = 1) (hb : d202307 p = 1) : d206996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22471 q = 1) (hb : d202307 q = 1) : d206985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22471, d206985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48139 q ha hb
    | true =>
      simp only [d22471, d206985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22472 q = 1) (hb : d202307 q = 1) : d206986 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22472, d206986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22472, d206986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22473 q = 1) (hb : d202307 q = 1) : d206987 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22473, d206987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22473, d206987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22474 q = 1) (hb : d202307 q = 1) : d206988 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22474, d206988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22474, d206988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22475 q = 1) (hb : d202307 q = 1) : d206989 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22475, d206989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22475, d206989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22477 q = 1) (hb : d202307 q = 1) : d206991 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22477, d206991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48142 q ha hb
    | true =>
      simp only [d22477, d206991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22478 q = 1) (hb : d202307 q = 1) : d206992 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22478, d206992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22478, d206992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22479 q = 1) (hb : d202307 q = 1) : d206993 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22479, d206993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22479, d206993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22480 q = 1) (hb : d202307 q = 1) : d206994 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22480, d206994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22480, d206994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22481 q = 1) (hb : d202307 q = 1) : d206995 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22481, d206995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22481, d206995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22482 q = 1) (hb : d202307 q = 1) : d206996 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22482, d206996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22482, d206996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48148 (p : Pattern) (ha : d22491 p = 1) (hb : d202307 p = 1) : d207005 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22477 q = 1) (hb : d202307 q = 1) : d206991 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22477, d206991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48142 q ha hb
    | true =>
      simp only [d22477, d206991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22478 q = 1) (hb : d202307 q = 1) : d206992 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22478, d206992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22478, d206992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22479 q = 1) (hb : d202307 q = 1) : d206993 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22479, d206993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22479, d206993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22480 q = 1) (hb : d202307 q = 1) : d206994 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22480, d206994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22480, d206994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22481 q = 1) (hb : d202307 q = 1) : d206995 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22481, d206995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22481, d206995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22491 q = 1) (hb : d202307 q = 1) : d207005 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22491, d207005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22491, d207005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48149 (p : Pattern) (ha : d22534 p = 1) (hb : d202307 p = 1) : d207038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22508 q = 1) (hb : d202307 q = 1) : d207013 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22508, d207013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22508, d207013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48127 q ha hb
  have h2 (q : Pattern) (ha : d22220 q = 1) (hb : d202307 q = 1) : d206813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d206813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48127 q ha hb
    | true =>
      simp only [d22220, d206813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22509 q = 1) (hb : d202307 q = 1) : d207014 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22509, d207014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22509, d207014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22221 q = 1) (hb : d202307 q = 1) : d206814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d206814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22221, d206814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22510 q = 1) (hb : d202307 q = 1) : d207015 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22510, d207015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22510, d207015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22511 q = 1) (hb : d202307 q = 1) : d207016 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22511, d207016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22511, d207016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22529 q = 1) (hb : d202307 q = 1) : d207033 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22529, d207033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22529, d207033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48130 q ha hb
  have h8 (q : Pattern) (ha : d22233 q = 1) (hb : d202307 q = 1) : d206825 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d206825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48130 q ha hb
    | true =>
      simp only [d22233, d206825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22530 q = 1) (hb : d202307 q = 1) : d207034 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22530, d207034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22530, d207034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22234 q = 1) (hb : d202307 q = 1) : d206826 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d206826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22234, d206826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22531 q = 1) (hb : d202307 q = 1) : d207035 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22531, d207035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22531, d207035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22532 q = 1) (hb : d202307 q = 1) : d207036 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22532, d207036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22532, d207036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22533 q = 1) (hb : d202307 q = 1) : d207037 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22533, d207037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22533, d207037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13490 q = 1) (hb : d202307 q = 1) : d206411 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13490, d206411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13490, d206411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48123 q ha hb
  have h15 (q : Pattern) (ha : d13351 q = 1) (hb : d202307 q = 1) : d206324 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48123 q ha hb
    | true =>
      simp only [d13351, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d13491 q = 1) (hb : d202307 q = 1) : d206412 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13491, d206412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d13491, d206412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13352 q = 1) (hb : d202307 q = 1) : d206325 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13352, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13492 q = 1) (hb : d202307 q = 1) : d206413 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13492, d206413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13492, d206413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13493 q = 1) (hb : d202307 q = 1) : d206414 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13493, d206414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d13493, d206414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d22523 q = 1) (hb : d202307 q = 1) : d207027 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22523, d207027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d22523, d207027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d22534 q = 1) (hb : d202307 q = 1) : d207038 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22534, d207038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22534, d207038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro48150 (p : Pattern) (ha : d22562 p = 1) (hb : d202307 p = 1) : d207066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22529 q = 1) (hb : d202307 q = 1) : d207033 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22529, d207033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22529, d207033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48130 q ha hb
  have h2 (q : Pattern) (ha : d22233 q = 1) (hb : d202307 q = 1) : d206825 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d206825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48130 q ha hb
    | true =>
      simp only [d22233, d206825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22530 q = 1) (hb : d202307 q = 1) : d207034 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22530, d207034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22530, d207034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22234 q = 1) (hb : d202307 q = 1) : d206826 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d206826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22234, d206826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22531 q = 1) (hb : d202307 q = 1) : d207035 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22531, d207035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22531, d207035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22532 q = 1) (hb : d202307 q = 1) : d207036 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22532, d207036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22532, d207036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22561 q = 1) (hb : d202307 q = 1) : d207065 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22561, d207065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22561, d207065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15412 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48132 q ha hb
  have h9 (q : Pattern) (ha : d10135 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48132 q ha hb
    | true =>
      simp only [d10135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15413 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10137 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15414 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15415 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15416 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22562 q = 1) (hb : d202307 q = 1) : d207066 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22562, d207066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22562, d207066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48151 (p : Pattern) (ha : d22568 p = 1) (hb : d202307 p = 1) : d207072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22563 q = 1) (hb : d202307 q = 1) : d207067 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22563, d207067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48149 q ha hb
    | true =>
      simp only [d22563, d207067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48150 q ha hb
  have h2 (q : Pattern) (ha : d22564 q = 1) (hb : d202307 q = 1) : d207068 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22564, d207068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22564, d207068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22565 q = 1) (hb : d202307 q = 1) : d207069 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22565, d207069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22565, d207069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22566 q = 1) (hb : d202307 q = 1) : d207070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22566, d207070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22566, d207070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22567 q = 1) (hb : d202307 q = 1) : d207071 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22567, d207071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22567, d207071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22568 q = 1) (hb : d202307 q = 1) : d207072 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22568, d207072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22568, d207072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48152 (p : Pattern) (ha : d22662 p = 1) (hb : d202307 p = 1) : d207099 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22569 q = 1) (hb : d202307 q = 1) : d207073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22569, d207073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48151 q ha hb
    | true =>
      simp only [d22569, d207073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22570 q = 1) (hb : d202307 q = 1) : d207074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22570, d207074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22570, d207074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22659 q = 1) (hb : d202307 q = 1) : d207096 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22659, d207096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22659, d207096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22660 q = 1) (hb : d202307 q = 1) : d207097 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22660, d207097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22660, d207097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22661 q = 1) (hb : d202307 q = 1) : d207098 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22661, d207098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22661, d207098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22662 q = 1) (hb : d202307 q = 1) : d207099 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22662, d207099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22662, d207099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48153 (p : Pattern) (ha : d22668 p = 1) (hb : d202307 p = 1) : d207105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22663 q = 1) (hb : d202307 q = 1) : d207100 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22663, d207100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48152 q ha hb
    | true =>
      simp only [d22663, d207100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22664 q = 1) (hb : d202307 q = 1) : d207101 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22664, d207101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22664, d207101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22665 q = 1) (hb : d202307 q = 1) : d207102 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22665, d207102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22665, d207102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22666 q = 1) (hb : d202307 q = 1) : d207103 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22666, d207103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22666, d207103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22667 q = 1) (hb : d202307 q = 1) : d207104 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22667, d207104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22667, d207104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22668 q = 1) (hb : d202307 q = 1) : d207105 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22668, d207105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22668, d207105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48154 (p : Pattern) (ha : d22296 p = 1) (hb : d202307 p = 1) : d206893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d202307 q = 1) : d206859 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d206859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48136 q ha hb
    | true =>
      simp only [d22262, d206859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d202307 q = 1) : d206860 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d206860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d206860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d202307 q = 1) : d206863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48137 q ha hb
    | true =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d202307 q = 1) : d206864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d202307 q = 1) : d206865 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d206865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d206865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22269 q = 1) (hb : d202307 q = 1) : d206866 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22269, d206866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22269, d206866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22295 q = 1) (hb : d202307 q = 1) : d206892 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22295, d206892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22295, d206892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22296 q = 1) (hb : d202307 q = 1) : d206893 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22296, d206893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22296, d206893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48155 (p : Pattern) (ha : d22298 p = 1) (hb : d202307 p = 1) : d206895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d202307 q = 1) : d206863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48137 q ha hb
    | true =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d202307 q = 1) : d206864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d202307 q = 1) : d206869 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d206869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d206869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22273 q = 1) (hb : d202307 q = 1) : d206870 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22273, d206870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22273, d206870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22297 q = 1) (hb : d202307 q = 1) : d206894 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22297, d206894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22297, d206894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22298 q = 1) (hb : d202307 q = 1) : d206895 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22298, d206895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22298, d206895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48156 (p : Pattern) (ha : d22305 p = 1) (hb : d202307 p = 1) : d206902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d202307 q = 1) : d206859 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d206859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48136 q ha hb
    | true =>
      simp only [d22262, d206859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d202307 q = 1) : d206860 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d206860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d206860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d202307 q = 1) : d206863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48137 q ha hb
    | true =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d202307 q = 1) : d206864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d202307 q = 1) : d206865 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d206865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d206865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22303 q = 1) (hb : d202307 q = 1) : d206900 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22303, d206900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22303, d206900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22304 q = 1) (hb : d202307 q = 1) : d206901 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22304, d206901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22304, d206901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22305 q = 1) (hb : d202307 q = 1) : d206902 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22305, d206902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22305, d206902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48157 (p : Pattern) (ha : d22308 p = 1) (hb : d202307 p = 1) : d206905 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d202307 q = 1) : d206863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48137 q ha hb
    | true =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d202307 q = 1) : d206864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d202307 q = 1) : d206869 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d206869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d206869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22306 q = 1) (hb : d202307 q = 1) : d206903 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22306, d206903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22306, d206903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22307 q = 1) (hb : d202307 q = 1) : d206904 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22307, d206904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22307, d206904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22308 q = 1) (hb : d202307 q = 1) : d206905 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22308, d206905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22308, d206905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48158 (p : Pattern) (ha : d10045 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1201 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10042 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10042, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10042, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10043 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10044 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10045 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10045, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10045, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro48159 (p : Pattern) (ha : d1199 p = 1) (hb : d202304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d820 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1199 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d1199, d202304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1199, d202304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48160 (p : Pattern) (ha : d1203 p = 1) (hb : d202304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d826 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1203 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d1203, d202304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1203, d202304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48161 (p : Pattern) (ha : d22312 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1200 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48159 q ha hb
    | true =>
      simp only [d1200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1201 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1660 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1660, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1660, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1204 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48160 q ha hb
    | true =>
      simp only [d1204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1205 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1661 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1661, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1661, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1662 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1663 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22312 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22312, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22312, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro48162 (p : Pattern) (ha : d22319 p = 1) (hb : d202307 p = 1) : d206910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22313 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48161 q ha hb
    | true =>
      simp only [d22313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22314 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22315 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22316 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10036 q = 1) (hb : d202307 q = 1) : d206585 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d206585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48121 q ha hb
    | true =>
      simp only [d10036, d206585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10038 q = 1) (hb : d202307 q = 1) : d206586 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d206586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10038, d206586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16859 q = 1) (hb : d202307 q = 1) : d206587 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16859, d206587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16859, d206587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16860 q = 1) (hb : d202307 q = 1) : d206588 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16860, d206588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16860, d206588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22317 q = 1) (hb : d202307 q = 1) : d206909 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22317, d206909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22317, d206909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10046 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48158 q ha hb
    | true =>
      simp only [d10046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10048 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15229 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15230 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d22226 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48128 q ha hb
    | true =>
      simp only [d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22227 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d22228 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22229 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d22229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d22318 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d22319 q = 1) (hb : d202307 q = 1) : d206910 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22319, d206910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22319, d206910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro48163 (p : Pattern) (ha : d22323 p = 1) (hb : d202307 p = 1) : d206917 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1529 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10056 q = 1) (hb : d202304 q = 1) : d10056 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10095 q = 1) (hb : d202306 q = 1) : d206914 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10095, d202306, d206914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10095, d202306, d206914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10096 q = 1) (hb : d202306 q = 1) : d206915 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10096, d206915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10096, d206915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10097 q = 1) (hb : d202306 q = 1) : d206916 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10097, d206916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10097, d206916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d22323 q = 1) (hb : d202307 q = 1) : d206917 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22323, d202307, d206917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22323, d202307, d206917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro48164 (p : Pattern) (ha : d22329 p = 1) (hb : d202307 p = 1) : d206923 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22324 q = 1) (hb : d202307 q = 1) : d206918 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22324, d206918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48163 q ha hb
    | true =>
      simp only [d22324, d206918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22325 q = 1) (hb : d202307 q = 1) : d206919 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22325, d206919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22325, d206919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22326 q = 1) (hb : d202307 q = 1) : d206920 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22326, d206920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22326, d206920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22327 q = 1) (hb : d202307 q = 1) : d206921 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22327, d206921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22327, d206921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13351 q = 1) (hb : d202307 q = 1) : d206324 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48123 q ha hb
    | true =>
      simp only [d13351, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13352 q = 1) (hb : d202307 q = 1) : d206325 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13352, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13353 q = 1) (hb : d202307 q = 1) : d206326 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13353, d206326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13353, d206326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13354 q = 1) (hb : d202307 q = 1) : d206327 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13354, d206327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13354, d206327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22328 q = 1) (hb : d202307 q = 1) : d206922 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22328, d206922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22328, d206922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22238 q = 1) (hb : d202307 q = 1) : d206830 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22238, d206830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22238, d206830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22329 q = 1) (hb : d202307 q = 1) : d206923 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22329, d206923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22329, d206923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48165 (p : Pattern) (ha : d22335 p = 1) (hb : d202307 p = 1) : d206929 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22320 q = 1) (hb : d202307 q = 1) : d206911 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22320, d206911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48162 q ha hb
    | true =>
      simp only [d22320, d206911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48129 q ha hb
  have h2 (q : Pattern) (ha : d22321 q = 1) (hb : d202307 q = 1) : d206912 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22321, d206912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22321, d206912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22322 q = 1) (hb : d202307 q = 1) : d206913 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22322, d206913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22322, d206913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22330 q = 1) (hb : d202307 q = 1) : d206924 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22330, d206924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48129 q ha hb
    | true =>
      simp only [d22330, d206924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48164 q ha hb
  have h5 (q : Pattern) (ha : d22331 q = 1) (hb : d202307 q = 1) : d206925 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22331, d206925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22331, d206925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22332 q = 1) (hb : d202307 q = 1) : d206926 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22332, d206926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22332, d206926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22333 q = 1) (hb : d202307 q = 1) : d206927 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22333, d206927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22333, d206927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22240 q = 1) (hb : d202307 q = 1) : d206832 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22240, d206832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48129 q ha hb
    | true =>
      simp only [d22240, d206832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48131 q ha hb
  have h9 (q : Pattern) (ha : d22241 q = 1) (hb : d202307 q = 1) : d206833 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22241, d206833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22241, d206833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22242 q = 1) (hb : d202307 q = 1) : d206834 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22242, d206834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22242, d206834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22250 q = 1) (hb : d202307 q = 1) : d206847 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22250, d206847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48131 q ha hb
    | true =>
      simp only [d22250, d206847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48134 q ha hb
  have h12 (q : Pattern) (ha : d22251 q = 1) (hb : d202307 q = 1) : d206848 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22251, d206848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22251, d206848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22252 q = 1) (hb : d202307 q = 1) : d206849 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22252, d206849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22252, d206849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22253 q = 1) (hb : d202307 q = 1) : d206850 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22253, d206850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22253, d206850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22334 q = 1) (hb : d202307 q = 1) : d206928 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22334, d206928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22334, d206928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22335 q = 1) (hb : d202307 q = 1) : d206929 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22335, d206929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d22335, d206929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro48166 (p : Pattern) (ha : d22346 p = 1) (hb : d202307 p = 1) : d206940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22336 q = 1) (hb : d202307 q = 1) : d206930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22336, d206930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48165 q ha hb
    | true =>
      simp only [d22336, d206930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22337 q = 1) (hb : d202307 q = 1) : d206931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22337, d206931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22337, d206931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22341 q = 1) (hb : d202307 q = 1) : d206935 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22341, d206935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48144 q ha hb
    | true =>
      simp only [d22341, d206935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22342 q = 1) (hb : d202307 q = 1) : d206936 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22342, d206936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22342, d206936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22343 q = 1) (hb : d202307 q = 1) : d206937 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22343, d206937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22343, d206937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22344 q = 1) (hb : d202307 q = 1) : d206938 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22344, d206938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22344, d206938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22345 q = 1) (hb : d202307 q = 1) : d206939 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22345, d206939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22345, d206939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22346 q = 1) (hb : d202307 q = 1) : d206940 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22346, d206940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22346, d206940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48167 (p : Pattern) (ha : d22421 p = 1) (hb : d202307 p = 1) : d206852 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22233 q = 1) (hb : d202307 q = 1) : d206825 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d206825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48130 q ha hb
    | true =>
      simp only [d22233, d206825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22234 q = 1) (hb : d202307 q = 1) : d206826 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d206826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22234, d206826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22235 q = 1) (hb : d202307 q = 1) : d206827 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22235, d206827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22235, d206827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22236 q = 1) (hb : d202307 q = 1) : d206828 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22236, d206828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22236, d206828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22254 q = 1) (hb : d202307 q = 1) : d206851 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22254, d206851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22254, d206851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22421 q = 1) (hb : d202307 q = 1) : d206852 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22421, d206852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22421, d206852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48168 (p : Pattern) (ha : d22427 p = 1) (hb : d202307 p = 1) : d206858 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22240 q = 1) (hb : d202307 q = 1) : d206832 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22240, d206832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48129 q ha hb
    | true =>
      simp only [d22240, d206832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48131 q ha hb
  have h2 (q : Pattern) (ha : d22241 q = 1) (hb : d202307 q = 1) : d206833 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22241, d206833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22241, d206833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22242 q = 1) (hb : d202307 q = 1) : d206834 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22242, d206834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22242, d206834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22250 q = 1) (hb : d202307 q = 1) : d206847 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22250, d206847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48131 q ha hb
    | true =>
      simp only [d22250, d206847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48134 q ha hb
  have h5 (q : Pattern) (ha : d22251 q = 1) (hb : d202307 q = 1) : d206848 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22251, d206848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22251, d206848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22252 q = 1) (hb : d202307 q = 1) : d206849 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22252, d206849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22252, d206849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22253 q = 1) (hb : d202307 q = 1) : d206850 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22253, d206850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22253, d206850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22422 q = 1) (hb : d202307 q = 1) : d206853 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22422, d206853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48131 q ha hb
    | true =>
      simp only [d22422, d206853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48167 q ha hb
  have h9 (q : Pattern) (ha : d22423 q = 1) (hb : d202307 q = 1) : d206854 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22423, d206854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22423, d206854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22424 q = 1) (hb : d202307 q = 1) : d206855 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22424, d206855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22424, d206855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22425 q = 1) (hb : d202307 q = 1) : d206856 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22425, d206856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22425, d206856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d22426 q = 1) (hb : d202307 q = 1) : d206857 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22426, d206857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22426, d206857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22427 q = 1) (hb : d202307 q = 1) : d206858 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22427, d206858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22427, d206858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro48169 (p : Pattern) (ha : d22433 p = 1) (hb : d202307 p = 1) : d206950 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22428 q = 1) (hb : d202307 q = 1) : d206859 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22428, d206859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48168 q ha hb
    | true =>
      simp only [d22428, d206859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22429 q = 1) (hb : d202307 q = 1) : d206860 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22429, d206860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22429, d206860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22430 q = 1) (hb : d202307 q = 1) : d206947 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22430, d206947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22430, d206947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22431 q = 1) (hb : d202307 q = 1) : d206948 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22431, d206948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22431, d206948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22432 q = 1) (hb : d202307 q = 1) : d206949 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22432, d206949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22432, d206949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22433 q = 1) (hb : d202307 q = 1) : d206950 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22433, d206950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22433, d206950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48170 (p : Pattern) (ha : d150201 p = 1) (hb : d202307 p = 1) : d206956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22299 q = 1) (hb : d202307 q = 1) : d206896 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22299, d206896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48154 q ha hb
    | true =>
      simp only [d22299, d206896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48155 q ha hb
  have h2 (q : Pattern) (ha : d22300 q = 1) (hb : d202307 q = 1) : d206897 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22300, d206897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22300, d206897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22301 q = 1) (hb : d202307 q = 1) : d206898 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22301, d206898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22301, d206898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22302 q = 1) (hb : d202307 q = 1) : d206899 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22302, d206899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22302, d206899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22309 q = 1) (hb : d202307 q = 1) : d206906 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22309, d206906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48156 q ha hb
    | true =>
      simp only [d22309, d206906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48157 q ha hb
  have h6 (q : Pattern) (ha : d22310 q = 1) (hb : d202307 q = 1) : d206907 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22310, d206907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22310, d206907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22311 q = 1) (hb : d202307 q = 1) : d206908 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22311, d206908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22311, d206908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22351 q = 1) (hb : d202307 q = 1) : d206945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22351, d206945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48166 q ha hb
    | true =>
      simp only [d22351, d206945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48145 q ha hb
  have h9 (q : Pattern) (ha : d150197 q = 1) (hb : d202307 q = 1) : d206946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150197, d206946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150197, d206946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d22434 q = 1) (hb : d202307 q = 1) : d206951 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22434, d206951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48169 q ha hb
    | true =>
      simp only [d22434, d206951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22435 q = 1) (hb : d202307 q = 1) : d206952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22435, d206952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22435, d206952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150198 q = 1) (hb : d202307 q = 1) : d206953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150198, d206953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150198, d206953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150199 q = 1) (hb : d202307 q = 1) : d206954 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150199, d206954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150199, d206954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150200 q = 1) (hb : d202307 q = 1) : d206955 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150200, d206955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150200, d206955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150201 q = 1) (hb : d202307 q = 1) : d206956 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150201, d206956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150201, d206956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48171 (p : Pattern) (ha : d22440 p = 1) (hb : d202307 p = 1) : d206957 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d202307 q = 1) : d206859 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d206859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48136 q ha hb
    | true =>
      simp only [d22262, d206859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d202307 q = 1) : d206860 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d206860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d206860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d202307 q = 1) : d206863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48137 q ha hb
    | true =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d202307 q = 1) : d206864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d202307 q = 1) : d206865 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d206865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d206865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22269 q = 1) (hb : d202307 q = 1) : d206866 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22269, d206866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22269, d206866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22295 q = 1) (hb : d202307 q = 1) : d206892 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22295, d206892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22295, d206892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22440 q = 1) (hb : d202307 q = 1) : d206957 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22440, d206957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22440, d206957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48172 (p : Pattern) (ha : d22441 p = 1) (hb : d202307 p = 1) : d206958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d202307 q = 1) : d206863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48137 q ha hb
    | true =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d202307 q = 1) : d206864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d202307 q = 1) : d206869 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d206869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d206869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22273 q = 1) (hb : d202307 q = 1) : d206870 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22273, d206870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22273, d206870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22297 q = 1) (hb : d202307 q = 1) : d206894 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22297, d206894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22297, d206894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22441 q = 1) (hb : d202307 q = 1) : d206958 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22441, d206958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22441, d206958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48173 (p : Pattern) (ha : d22446 p = 1) (hb : d202307 p = 1) : d206963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d202307 q = 1) : d206859 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d206859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48136 q ha hb
    | true =>
      simp only [d22262, d206859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d202307 q = 1) : d206860 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d206860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d206860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d202307 q = 1) : d206863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48137 q ha hb
    | true =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d202307 q = 1) : d206864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d202307 q = 1) : d206865 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d206865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d206865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22303 q = 1) (hb : d202307 q = 1) : d206900 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22303, d206900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22303, d206900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22304 q = 1) (hb : d202307 q = 1) : d206901 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22304, d206901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22304, d206901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22446 q = 1) (hb : d202307 q = 1) : d206963 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22446, d206963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22446, d206963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48174 (p : Pattern) (ha : d22447 p = 1) (hb : d202307 p = 1) : d206964 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d202307 q = 1) : d206863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48137 q ha hb
    | true =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d202307 q = 1) : d206864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d202307 q = 1) : d206869 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d206869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d206869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22306 q = 1) (hb : d202307 q = 1) : d206903 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22306, d206903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22306, d206903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22307 q = 1) (hb : d202307 q = 1) : d206904 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22307, d206904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22307, d206904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22447 q = 1) (hb : d202307 q = 1) : d206964 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22447, d206964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22447, d206964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48175 (p : Pattern) (ha : d22451 p = 1) (hb : d202307 p = 1) : d206968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22336 q = 1) (hb : d202307 q = 1) : d206930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22336, d206930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48165 q ha hb
    | true =>
      simp only [d22336, d206930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22337 q = 1) (hb : d202307 q = 1) : d206931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22337, d206931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22337, d206931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22341 q = 1) (hb : d202307 q = 1) : d206935 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22341, d206935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48144 q ha hb
    | true =>
      simp only [d22341, d206935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22342 q = 1) (hb : d202307 q = 1) : d206936 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22342, d206936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22342, d206936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22343 q = 1) (hb : d202307 q = 1) : d206937 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22343, d206937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22343, d206937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22344 q = 1) (hb : d202307 q = 1) : d206938 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22344, d206938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22344, d206938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22345 q = 1) (hb : d202307 q = 1) : d206939 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22345, d206939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22345, d206939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22451 q = 1) (hb : d202307 q = 1) : d206968 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22451, d206968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22451, d206968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48176 (p : Pattern) (ha : d22452 p = 1) (hb : d202307 p = 1) : d206969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22341 q = 1) (hb : d202307 q = 1) : d206935 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22341, d206935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48144 q ha hb
    | true =>
      simp only [d22341, d206935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22342 q = 1) (hb : d202307 q = 1) : d206936 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22342, d206936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22342, d206936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d202307 q = 1) : d206863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48137 q ha hb
    | true =>
      simp only [d22266, d206863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d202307 q = 1) : d206864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d206864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22347 q = 1) (hb : d202307 q = 1) : d206941 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22347, d206941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22347, d206941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22348 q = 1) (hb : d202307 q = 1) : d206942 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22348, d206942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22348, d206942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22349 q = 1) (hb : d202307 q = 1) : d206943 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22349, d206943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22349, d206943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22452 q = 1) (hb : d202307 q = 1) : d206969 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22452, d206969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22452, d206969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48177 (p : Pattern) (ha : d22458 p = 1) (hb : d202307 p = 1) : d206972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22428 q = 1) (hb : d202307 q = 1) : d206859 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22428, d206859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48168 q ha hb
    | true =>
      simp only [d22428, d206859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22429 q = 1) (hb : d202307 q = 1) : d206860 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22429, d206860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22429, d206860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22430 q = 1) (hb : d202307 q = 1) : d206947 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22430, d206947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22430, d206947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22431 q = 1) (hb : d202307 q = 1) : d206948 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22431, d206948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22431, d206948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22432 q = 1) (hb : d202307 q = 1) : d206949 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22432, d206949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22432, d206949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22458 q = 1) (hb : d202307 q = 1) : d206972 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22458, d206972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22458, d206972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48178 (p : Pattern) (ha : d150206 p = 1) (hb : d202307 p = 1) : d206978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22299 q = 1) (hb : d202307 q = 1) : d206896 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22299, d206896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48154 q ha hb
    | true =>
      simp only [d22299, d206896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48155 q ha hb
  have h2 (q : Pattern) (ha : d22300 q = 1) (hb : d202307 q = 1) : d206897 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22300, d206897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22300, d206897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22301 q = 1) (hb : d202307 q = 1) : d206898 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22301, d206898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22301, d206898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22302 q = 1) (hb : d202307 q = 1) : d206899 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22302, d206899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22302, d206899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22309 q = 1) (hb : d202307 q = 1) : d206906 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22309, d206906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48156 q ha hb
    | true =>
      simp only [d22309, d206906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48157 q ha hb
  have h6 (q : Pattern) (ha : d22310 q = 1) (hb : d202307 q = 1) : d206907 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22310, d206907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22310, d206907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22311 q = 1) (hb : d202307 q = 1) : d206908 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22311, d206908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22311, d206908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22351 q = 1) (hb : d202307 q = 1) : d206945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22351, d206945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48166 q ha hb
    | true =>
      simp only [d22351, d206945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48145 q ha hb
  have h9 (q : Pattern) (ha : d150197 q = 1) (hb : d202307 q = 1) : d206946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150197, d206946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150197, d206946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d22434 q = 1) (hb : d202307 q = 1) : d206951 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22434, d206951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48169 q ha hb
    | true =>
      simp only [d22434, d206951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22435 q = 1) (hb : d202307 q = 1) : d206952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22435, d206952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22435, d206952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150198 q = 1) (hb : d202307 q = 1) : d206953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150198, d206953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150198, d206953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150199 q = 1) (hb : d202307 q = 1) : d206954 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150199, d206954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150199, d206954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150200 q = 1) (hb : d202307 q = 1) : d206955 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150200, d206955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150200, d206955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22442 q = 1) (hb : d202307 q = 1) : d206959 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22442, d206959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48171 q ha hb
    | true =>
      simp only [d22442, d206959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48172 q ha hb
  have h16 (q : Pattern) (ha : d22443 q = 1) (hb : d202307 q = 1) : d206960 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22443, d206960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22443, d206960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22444 q = 1) (hb : d202307 q = 1) : d206961 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22444, d206961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d22444, d206961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d22445 q = 1) (hb : d202307 q = 1) : d206962 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22445, d206962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22445, d206962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d22448 q = 1) (hb : d202307 q = 1) : d206965 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22448, d206965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48173 q ha hb
    | true =>
      simp only [d22448, d206965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48174 q ha hb
  have h20 (q : Pattern) (ha : d22449 q = 1) (hb : d202307 q = 1) : d206966 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22449, d206966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22449, d206966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d22450 q = 1) (hb : d202307 q = 1) : d206967 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22450, d206967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d22450, d206967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d22453 q = 1) (hb : d202307 q = 1) : d206970 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22453, d206970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48175 q ha hb
    | true =>
      simp only [d22453, d206970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48176 q ha hb
  have h23 (q : Pattern) (ha : d150202 q = 1) (hb : d202307 q = 1) : d206971 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150202, d206971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d150202, d206971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d22459 q = 1) (hb : d202307 q = 1) : d206973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22459, d206973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48177 q ha hb
    | true =>
      simp only [d22459, d206973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d22460 q = 1) (hb : d202307 q = 1) : d206974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22460, d206974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d22460, d206974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d150203 q = 1) (hb : d202307 q = 1) : d206975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150203, d206975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150203, d206975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d150204 q = 1) (hb : d202307 q = 1) : d206976 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150204, d206976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150204, d206976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d150205 q = 1) (hb : d202307 q = 1) : d206977 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150205, d206977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d150205, d206977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d150206 q = 1) (hb : d202307 q = 1) : d206978 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150206, d206978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150206, d206978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro48179 (p : Pattern) (ha : d150213 p = 1) (hb : d202307 p = 1) : d207003 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22453 q = 1) (hb : d202307 q = 1) : d206970 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22453, d206970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48175 q ha hb
    | true =>
      simp only [d22453, d206970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48176 q ha hb
  have h2 (q : Pattern) (ha : d150202 q = 1) (hb : d202307 q = 1) : d206971 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150202, d206971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150202, d206971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22459 q = 1) (hb : d202307 q = 1) : d206973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22459, d206973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48177 q ha hb
    | true =>
      simp only [d22459, d206973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22460 q = 1) (hb : d202307 q = 1) : d206974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22460, d206974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22460, d206974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150203 q = 1) (hb : d202307 q = 1) : d206975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150203, d206975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150203, d206975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150211 q = 1) (hb : d202307 q = 1) : d207001 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150211, d207001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150211, d207001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150212 q = 1) (hb : d202307 q = 1) : d207002 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150212, d207002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150212, d207002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150213 q = 1) (hb : d202307 q = 1) : d207003 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150213, d207003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150213, d207003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48180 (p : Pattern) (ha : d22507 p = 1) (hb : d202307 p = 1) : d207012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22497 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48161 q ha hb
  have h2 (q : Pattern) (ha : d22313 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48161 q ha hb
    | true =>
      simp only [d22313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22498 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22314 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22499 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22500 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17004 q = 1) (hb : d202307 q = 1) : d206694 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d206694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17004, d206694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48121 q ha hb
  have h8 (q : Pattern) (ha : d10036 q = 1) (hb : d202307 q = 1) : d206585 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d206585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48121 q ha hb
    | true =>
      simp only [d10036, d206585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17005 q = 1) (hb : d202307 q = 1) : d206695 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, d206695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17005, d206695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10038 q = 1) (hb : d202307 q = 1) : d206586 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d206586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10038, d206586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17006 q = 1) (hb : d202307 q = 1) : d206696 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17006, d206696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17006, d206696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17007 q = 1) (hb : d202307 q = 1) : d206697 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17007, d206697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17007, d206697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22501 q = 1) (hb : d202307 q = 1) : d207011 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22501, d207011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22501, d207011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15380 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48158 q ha hb
  have h15 (q : Pattern) (ha : d10046 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48158 q ha hb
    | true =>
      simp only [d10046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d15381 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10048 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d15382 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15383 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d15383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d22502 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48128 q ha hb
  have h21 (q : Pattern) (ha : d22226 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48128 q ha hb
    | true =>
      simp only [d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d22503 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d22503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d22227 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d22504 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d22504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d22505 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d22505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d22506 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d22506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d22507 q = 1) (hb : d202307 q = 1) : d207012 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22507, d207012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22507, d207012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro48181 (p : Pattern) (ha : d22514 p = 1) (hb : d202307 p = 1) : d207018 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17004 q = 1) (hb : d202307 q = 1) : d206694 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d206694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17004, d206694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48121 q ha hb
  have h2 (q : Pattern) (ha : d10036 q = 1) (hb : d202307 q = 1) : d206585 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d206585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48121 q ha hb
    | true =>
      simp only [d10036, d206585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17005 q = 1) (hb : d202307 q = 1) : d206695 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, d206695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17005, d206695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10038 q = 1) (hb : d202307 q = 1) : d206586 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d206586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10038, d206586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17006 q = 1) (hb : d202307 q = 1) : d206696 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17006, d206696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17006, d206696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17007 q = 1) (hb : d202307 q = 1) : d206697 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17007, d206697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17007, d206697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22508 q = 1) (hb : d202307 q = 1) : d207013 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22508, d207013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22508, d207013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48127 q ha hb
  have h8 (q : Pattern) (ha : d22220 q = 1) (hb : d202307 q = 1) : d206813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d206813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48127 q ha hb
    | true =>
      simp only [d22220, d206813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22509 q = 1) (hb : d202307 q = 1) : d207014 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22509, d207014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22509, d207014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22221 q = 1) (hb : d202307 q = 1) : d206814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d206814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22221, d206814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22510 q = 1) (hb : d202307 q = 1) : d207015 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22510, d207015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22510, d207015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22511 q = 1) (hb : d202307 q = 1) : d207016 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22511, d207016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22511, d207016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22512 q = 1) (hb : d202307 q = 1) : d207017 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22512, d207017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22512, d207017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22502 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48128 q ha hb
  have h15 (q : Pattern) (ha : d22226 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48128 q ha hb
    | true =>
      simp only [d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d22503 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22227 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d22504 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d22504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d22505 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d22505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d13490 q = 1) (hb : d202307 q = 1) : d206411 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13490, d206411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13490, d206411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48123 q ha hb
  have h21 (q : Pattern) (ha : d13351 q = 1) (hb : d202307 q = 1) : d206324 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48123 q ha hb
    | true =>
      simp only [d13351, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d13491 q = 1) (hb : d202307 q = 1) : d206412 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13491, d206412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d13491, d206412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d13352 q = 1) (hb : d202307 q = 1) : d206325 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d13352, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d13492 q = 1) (hb : d202307 q = 1) : d206413 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13492, d206413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d13492, d206413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d13493 q = 1) (hb : d202307 q = 1) : d206414 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13493, d206414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13493, d206414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d22513 q = 1) (hb : d202307 q = 1) : d206699 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22513, d206699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d22513, d206699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d22514 q = 1) (hb : d202307 q = 1) : d207018 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22514, d207018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22514, d207018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro48182 (p : Pattern) (ha : d22524 p = 1) (hb : d202307 p = 1) : d207028 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22518 q = 1) (hb : d202307 q = 1) : d207022 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22518, d207022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22518, d207022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48163 q ha hb
  have h2 (q : Pattern) (ha : d22324 q = 1) (hb : d202307 q = 1) : d206918 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22324, d206918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48163 q ha hb
    | true =>
      simp only [d22324, d206918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22519 q = 1) (hb : d202307 q = 1) : d207023 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22519, d207023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22519, d207023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22325 q = 1) (hb : d202307 q = 1) : d206919 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22325, d206919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22325, d206919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22520 q = 1) (hb : d202307 q = 1) : d207024 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22520, d207024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22520, d207024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22521 q = 1) (hb : d202307 q = 1) : d207025 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22521, d207025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22521, d207025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13490 q = 1) (hb : d202307 q = 1) : d206411 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13490, d206411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13490, d206411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48123 q ha hb
  have h8 (q : Pattern) (ha : d13351 q = 1) (hb : d202307 q = 1) : d206324 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48123 q ha hb
    | true =>
      simp only [d13351, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13491 q = 1) (hb : d202307 q = 1) : d206412 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13491, d206412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13491, d206412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13352 q = 1) (hb : d202307 q = 1) : d206325 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13352, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13492 q = 1) (hb : d202307 q = 1) : d206413 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13492, d206413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13492, d206413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13493 q = 1) (hb : d202307 q = 1) : d206414 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13493, d206414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13493, d206414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22522 q = 1) (hb : d202307 q = 1) : d207026 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22522, d207026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22522, d207026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22523 q = 1) (hb : d202307 q = 1) : d207027 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22523, d207027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22523, d207027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22524 q = 1) (hb : d202307 q = 1) : d207028 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22524, d207028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22524, d207028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48183 (p : Pattern) (ha : d22543 p = 1) (hb : d202307 p = 1) : d207047 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22538 q = 1) (hb : d202307 q = 1) : d207042 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22538, d207042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22538, d207042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48133 q ha hb
  have h2 (q : Pattern) (ha : d22244 q = 1) (hb : d202307 q = 1) : d206841 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22244, d206841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48133 q ha hb
    | true =>
      simp only [d22244, d206841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22539 q = 1) (hb : d202307 q = 1) : d207043 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22539, d207043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22539, d207043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22245 q = 1) (hb : d202307 q = 1) : d206842 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22245, d206842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22245, d206842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22540 q = 1) (hb : d202307 q = 1) : d207044 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22540, d207044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22540, d207044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22541 q = 1) (hb : d202307 q = 1) : d207045 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22541, d207045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22541, d207045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22542 q = 1) (hb : d202307 q = 1) : d207046 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22542, d207046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22542, d207046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15412 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48132 q ha hb
  have h9 (q : Pattern) (ha : d10135 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48132 q ha hb
    | true =>
      simp only [d10135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15413 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10137 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15414 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15415 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15416 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22543 q = 1) (hb : d202307 q = 1) : d207047 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22543, d207047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22543, d207047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48184 (p : Pattern) (ha : d22549 p = 1) (hb : d202307 p = 1) : d207053 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22515 q = 1) (hb : d202307 q = 1) : d207019 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22515, d207019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48180 q ha hb
    | true =>
      simp only [d22515, d207019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48181 q ha hb
  have h2 (q : Pattern) (ha : d22516 q = 1) (hb : d202307 q = 1) : d207020 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22516, d207020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22516, d207020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22517 q = 1) (hb : d202307 q = 1) : d207021 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22517, d207021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22517, d207021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22525 q = 1) (hb : d202307 q = 1) : d207029 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22525, d207029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48181 q ha hb
    | true =>
      simp only [d22525, d207029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48182 q ha hb
  have h5 (q : Pattern) (ha : d22526 q = 1) (hb : d202307 q = 1) : d207030 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22526, d207030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22526, d207030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22527 q = 1) (hb : d202307 q = 1) : d207031 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22527, d207031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22527, d207031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22528 q = 1) (hb : d202307 q = 1) : d207032 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22528, d207032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22528, d207032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22535 q = 1) (hb : d202307 q = 1) : d207039 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22535, d207039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48181 q ha hb
    | true =>
      simp only [d22535, d207039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48149 q ha hb
  have h9 (q : Pattern) (ha : d22536 q = 1) (hb : d202307 q = 1) : d207040 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22536, d207040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22536, d207040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22537 q = 1) (hb : d202307 q = 1) : d207041 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22537, d207041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22537, d207041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22544 q = 1) (hb : d202307 q = 1) : d207048 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22544, d207048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48149 q ha hb
    | true =>
      simp only [d22544, d207048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48183 q ha hb
  have h12 (q : Pattern) (ha : d22545 q = 1) (hb : d202307 q = 1) : d207049 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22545, d207049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22545, d207049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22546 q = 1) (hb : d202307 q = 1) : d207050 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22546, d207050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22546, d207050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22547 q = 1) (hb : d202307 q = 1) : d207051 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22547, d207051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22547, d207051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22548 q = 1) (hb : d202307 q = 1) : d207052 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22548, d207052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22548, d207052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22549 q = 1) (hb : d202307 q = 1) : d207053 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22549, d207053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d22549, d207053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro48185 (p : Pattern) (ha : d22554 p = 1) (hb : d202307 p = 1) : d207058 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22535 q = 1) (hb : d202307 q = 1) : d207039 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22535, d207039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48181 q ha hb
    | true =>
      simp only [d22535, d207039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48149 q ha hb
  have h2 (q : Pattern) (ha : d22536 q = 1) (hb : d202307 q = 1) : d207040 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22536, d207040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22536, d207040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22537 q = 1) (hb : d202307 q = 1) : d207041 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22537, d207041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22537, d207041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22544 q = 1) (hb : d202307 q = 1) : d207048 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22544, d207048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48149 q ha hb
    | true =>
      simp only [d22544, d207048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48183 q ha hb
  have h5 (q : Pattern) (ha : d22545 q = 1) (hb : d202307 q = 1) : d207049 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22545, d207049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22545, d207049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22546 q = 1) (hb : d202307 q = 1) : d207050 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22546, d207050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22546, d207050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22547 q = 1) (hb : d202307 q = 1) : d207051 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22547, d207051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22547, d207051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22552 q = 1) (hb : d202307 q = 1) : d207056 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22552, d207056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22552, d207056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22553 q = 1) (hb : d202307 q = 1) : d207057 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22553, d207057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22553, d207057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22554 q = 1) (hb : d202307 q = 1) : d207058 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22554, d207058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22554, d207058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro48186 (p : Pattern) (ha : d22560 p = 1) (hb : d202307 p = 1) : d207064 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22550 q = 1) (hb : d202307 q = 1) : d207054 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22550, d207054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48184 q ha hb
    | true =>
      simp only [d22550, d207054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22551 q = 1) (hb : d202307 q = 1) : d207055 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22551, d207055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22551, d207055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22555 q = 1) (hb : d202307 q = 1) : d207059 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22555, d207059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48185 q ha hb
    | true =>
      simp only [d22555, d207059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22556 q = 1) (hb : d202307 q = 1) : d207060 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22556, d207060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22556, d207060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22557 q = 1) (hb : d202307 q = 1) : d207061 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22557, d207061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22557, d207061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22558 q = 1) (hb : d202307 q = 1) : d207062 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22558, d207062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22558, d207062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22559 q = 1) (hb : d202307 q = 1) : d207063 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22559, d207063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22559, d207063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22560 q = 1) (hb : d202307 q = 1) : d207064 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22560, d207064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22560, d207064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48187 (p : Pattern) (ha : d22574 p = 1) (hb : d202307 p = 1) : d207078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22555 q = 1) (hb : d202307 q = 1) : d207059 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22555, d207059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48185 q ha hb
    | true =>
      simp only [d22555, d207059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22556 q = 1) (hb : d202307 q = 1) : d207060 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22556, d207060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22556, d207060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22569 q = 1) (hb : d202307 q = 1) : d207073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22569, d207073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48151 q ha hb
    | true =>
      simp only [d22569, d207073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22570 q = 1) (hb : d202307 q = 1) : d207074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22570, d207074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22570, d207074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22571 q = 1) (hb : d202307 q = 1) : d207075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22571, d207075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22571, d207075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22572 q = 1) (hb : d202307 q = 1) : d207076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22572, d207076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22572, d207076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22573 q = 1) (hb : d202307 q = 1) : d207077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22573, d207077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22573, d207077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22574 q = 1) (hb : d202307 q = 1) : d207078 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22574, d207078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22574, d207078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48188 (p : Pattern) (ha : d22639 p = 1) (hb : d202307 p = 1) : d207066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22529 q = 1) (hb : d202307 q = 1) : d207033 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22529, d207033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22529, d207033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48130 q ha hb
  have h2 (q : Pattern) (ha : d22233 q = 1) (hb : d202307 q = 1) : d206825 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d206825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48130 q ha hb
    | true =>
      simp only [d22233, d206825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22530 q = 1) (hb : d202307 q = 1) : d207034 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22530, d207034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22530, d207034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22234 q = 1) (hb : d202307 q = 1) : d206826 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d206826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22234, d206826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22531 q = 1) (hb : d202307 q = 1) : d207035 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22531, d207035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22531, d207035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22532 q = 1) (hb : d202307 q = 1) : d207036 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22532, d207036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22532, d207036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22561 q = 1) (hb : d202307 q = 1) : d207065 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22561, d207065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22561, d207065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22639 q = 1) (hb : d202307 q = 1) : d207066 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22639, d207066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22639, d207066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48189 (p : Pattern) (ha : d22645 p = 1) (hb : d202307 p = 1) : d207082 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22535 q = 1) (hb : d202307 q = 1) : d207039 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22535, d207039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48181 q ha hb
    | true =>
      simp only [d22535, d207039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48149 q ha hb
  have h2 (q : Pattern) (ha : d22536 q = 1) (hb : d202307 q = 1) : d207040 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22536, d207040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22536, d207040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22537 q = 1) (hb : d202307 q = 1) : d207041 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22537, d207041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22537, d207041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22544 q = 1) (hb : d202307 q = 1) : d207048 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22544, d207048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48149 q ha hb
    | true =>
      simp only [d22544, d207048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48183 q ha hb
  have h5 (q : Pattern) (ha : d22545 q = 1) (hb : d202307 q = 1) : d207049 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22545, d207049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22545, d207049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22546 q = 1) (hb : d202307 q = 1) : d207050 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22546, d207050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22546, d207050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22547 q = 1) (hb : d202307 q = 1) : d207051 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22547, d207051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22547, d207051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22640 q = 1) (hb : d202307 q = 1) : d207067 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22640, d207067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48149 q ha hb
    | true =>
      simp only [d22640, d207067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48188 q ha hb
  have h9 (q : Pattern) (ha : d22641 q = 1) (hb : d202307 q = 1) : d207068 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22641, d207068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22641, d207068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22642 q = 1) (hb : d202307 q = 1) : d207069 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22642, d207069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22642, d207069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22643 q = 1) (hb : d202307 q = 1) : d207070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22643, d207070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22643, d207070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d22644 q = 1) (hb : d202307 q = 1) : d207081 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22644, d207081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22644, d207081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22645 q = 1) (hb : d202307 q = 1) : d207082 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22645, d207082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22645, d207082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro48190 (p : Pattern) (ha : d22651 p = 1) (hb : d202307 p = 1) : d207088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22646 q = 1) (hb : d202307 q = 1) : d207083 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22646, d207083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48189 q ha hb
    | true =>
      simp only [d22646, d207083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22647 q = 1) (hb : d202307 q = 1) : d207084 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22647, d207084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22647, d207084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22648 q = 1) (hb : d202307 q = 1) : d207085 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22648, d207085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22648, d207085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22649 q = 1) (hb : d202307 q = 1) : d207086 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22649, d207086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22649, d207086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22650 q = 1) (hb : d202307 q = 1) : d207087 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22650, d207087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22650, d207087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22651 q = 1) (hb : d202307 q = 1) : d207088 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22651, d207088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22651, d207088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48191 (p : Pattern) (ha : d150223 p = 1) (hb : d202307 p = 1) : d207094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22575 q = 1) (hb : d202307 q = 1) : d207079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22575, d207079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48186 q ha hb
    | true =>
      simp only [d22575, d207079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48187 q ha hb
  have h2 (q : Pattern) (ha : d150219 q = 1) (hb : d202307 q = 1) : d207080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150219, d207080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150219, d207080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22652 q = 1) (hb : d202307 q = 1) : d207089 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22652, d207089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48190 q ha hb
    | true =>
      simp only [d22652, d207089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22653 q = 1) (hb : d202307 q = 1) : d207090 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22653, d207090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22653, d207090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150220 q = 1) (hb : d202307 q = 1) : d207091 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150220, d207091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150220, d207091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150221 q = 1) (hb : d202307 q = 1) : d207092 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150221, d207092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150221, d207092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150222 q = 1) (hb : d202307 q = 1) : d207093 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150222, d207093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150222, d207093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150223 q = 1) (hb : d202307 q = 1) : d207094 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150223, d207094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150223, d207094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48192 (p : Pattern) (ha : d150229 p = 1) (hb : d202307 p = 1) : d207111 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22282 q = 1) (hb : d202307 q = 1) : d206879 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22282, d206879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22282, d206879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48140 q ha hb
  have h2 (q : Pattern) (ha : d22283 q = 1) (hb : d202307 q = 1) : d206880 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22283, d206880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22283, d206880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22292 q = 1) (hb : d202307 q = 1) : d206889 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22292, d206889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48140 q ha hb
    | true =>
      simp only [d22292, d206889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48143 q ha hb
  have h4 (q : Pattern) (ha : d22293 q = 1) (hb : d202307 q = 1) : d206890 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22293, d206890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22293, d206890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22294 q = 1) (hb : d202307 q = 1) : d206891 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d22294, d206891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22294, d206891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150207 q = 1) (hb : d202307 q = 1) : d206979 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150207, d206979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48170 q ha hb
    | true =>
      simp only [d150207, d206979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48178 q ha hb
  have h7 (q : Pattern) (ha : d22483 q = 1) (hb : d202307 q = 1) : d206997 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22483, d206997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48146 q ha hb
    | true =>
      simp only [d22483, d206997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48147 q ha hb
  have h8 (q : Pattern) (ha : d150208 q = 1) (hb : d202307 q = 1) : d206998 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150208, d206998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150208, d206998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150209 q = 1) (hb : d202307 q = 1) : d206999 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150209, d206999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150209, d206999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d150210 q = 1) (hb : d202307 q = 1) : d207000 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150210, d207000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150210, d207000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150214 q = 1) (hb : d202307 q = 1) : d207004 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150214, d207004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150214, d207004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48179 q ha hb
  have h12 (q : Pattern) (ha : d22492 q = 1) (hb : d202307 q = 1) : d207006 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22492, d207006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22492, d207006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48148 q ha hb
  have h13 (q : Pattern) (ha : d150215 q = 1) (hb : d202307 q = 1) : d207007 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150215, d207007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150215, d207007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150216 q = 1) (hb : d202307 q = 1) : d207008 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150216, d207008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150216, d207008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150217 q = 1) (hb : d202307 q = 1) : d207009 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150217, d207009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150217, d207009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d150218 q = 1) (hb : d202307 q = 1) : d207010 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150218, d207010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150218, d207010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150224 q = 1) (hb : d202307 q = 1) : d207095 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150224, d207095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150224, d207095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48191 q ha hb
  have h18 (q : Pattern) (ha : d22669 q = 1) (hb : d202307 q = 1) : d207106 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22669, d207106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22669, d207106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48153 q ha hb
  have h19 (q : Pattern) (ha : d150225 q = 1) (hb : d202307 q = 1) : d207107 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150225, d207107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150225, d207107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d150226 q = 1) (hb : d202307 q = 1) : d207108 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150226, d207108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150226, d207108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d150227 q = 1) (hb : d202307 q = 1) : d207109 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150227, d207109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150227, d207109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d150228 q = 1) (hb : d202307 q = 1) : d207110 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150228, d207110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150228, d207110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d150229 q = 1) (hb : d202307 q = 1) : d207111 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150229, d207111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150229, d207111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro48193 (p : Pattern) (ha : d150235 p = 1) (hb : d202307 p = 1) : d207117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150230 q = 1) (hb : d202307 q = 1) : d207112 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150230, d207112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150230, d207112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48192 q ha hb
  have h2 (q : Pattern) (ha : d150231 q = 1) (hb : d202307 q = 1) : d207113 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150231, d207113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150231, d207113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150232 q = 1) (hb : d202307 q = 1) : d207114 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150232, d207114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150232, d207114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150233 q = 1) (hb : d202307 q = 1) : d207115 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150233, d207115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150233, d207115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150234 q = 1) (hb : d202307 q = 1) : d207116 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150234, d207116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150234, d207116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150235 q = 1) (hb : d202307 q = 1) : d207117 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150235, d207117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150235, d207117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48194 (p : Pattern) (ha : d2000 p = 1) (hb : d202304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1999 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2000 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2000, d202304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2000, d202304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48195 (p : Pattern) (ha : d2003 p = 1) (hb : d202304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2002 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2003 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2003, d202304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2003, d202304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48196 (p : Pattern) (ha : d2007 p = 1) (hb : d202304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2006 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2007 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2007, d202304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2007, d202304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48197 (p : Pattern) (ha : d10342 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2004 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48194 q ha hb
    | true =>
      simp only [d2004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48195 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2008 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48196 q ha hb
  have h4 (q : Pattern) (ha : d2009 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2010 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2010, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2010, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2011 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2012 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d10342 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10342, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10342, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro48198 (p : Pattern) (ha : d10352 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2009 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10349 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10349, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10349, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10350 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10351 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10352 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10352, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10352, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro48199 (p : Pattern) (ha : d2015 p = 1) (hb : d202304 p = 1) : d32687 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1999 q = 1) : d1999 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2014 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2015 q = 1) (hb : d202304 q = 1) : d32687 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2015, d202304, d32687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2015, d202304, d32687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48200 (p : Pattern) (ha : d2019 p = 1) (hb : d202304 p = 1) : d32698 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2002 q = 1) : d2002 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2018 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2019 q = 1) (hb : d202304 q = 1) : d32698 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2019, d202304, d32698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2019, d202304, d32698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48201 (p : Pattern) (ha : d2023 p = 1) (hb : d202304 p = 1) : d10054 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2006 q = 1) : d2006 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2022 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2023 q = 1) (hb : d202304 q = 1) : d10054 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2023, d202304, d10054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2023, d202304, d10054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48202 (p : Pattern) (ha : d2028 p = 1) (hb : d202304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2027 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2028 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2028, d202304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2028, d202304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48203 (p : Pattern) (ha : d10363 p = 1) (hb : d202307 p = 1) : d207125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2009 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2020 q = 1) (hb : d202304 q = 1) : d32699 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d32699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48199 q ha hb
    | true =>
      simp only [d2020, d32699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48200 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2024 q = 1) (hb : d202304 q = 1) : d10055 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d10055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2024, d10055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48201 q ha hb
  have h4 (q : Pattern) (ha : d2025 q = 1) (hb : d202304 q = 1) : d32700 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d32700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2025, d32700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2026 q = 1) (hb : d202306 q = 1) : d207122 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2026, d202306, d207122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2026, d202306, d207122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2029 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48202 q ha hb
    | true =>
      simp only [d2029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d2030 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d2031 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2031, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2031, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2032 q = 1) (hb : d202306 q = 1) : d207123 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2032, d207123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2032, d207123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d2033 q = 1) (hb : d202306 q = 1) : d207124 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2033, d207124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2033, d207124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10363 q = 1) (hb : d202307 q = 1) : d207125 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10363, d202307, d207125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10363, d202307, d207125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h13 p ha hb
theorem andIntro48204 (p : Pattern) (ha : d13677 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2025 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5715 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5715, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5715, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5716 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5717 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13677 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13677, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13677, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro48205 (p : Pattern) (ha : d22686 p = 1) (hb : d202307 p = 1) : d207131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10343 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48197 q ha hb
    | true =>
      simp only [d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10345 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17225 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17226 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10364 q = 1) (hb : d202307 q = 1) : d207126 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d207126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48203 q ha hb
    | true =>
      simp only [d10364, d207126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10366 q = 1) (hb : d202307 q = 1) : d207127 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d207127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10366, d207127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17153 q = 1) (hb : d202307 q = 1) : d207128 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, d207128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17153, d207128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17154 q = 1) (hb : d202307 q = 1) : d207129 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17154, d207129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17154, d207129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22685 q = 1) (hb : d202307 q = 1) : d207130 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22685, d207130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22685, d207130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10353 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48198 q ha hb
    | true =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10355 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13675 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13676 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d13678 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48204 q ha hb
    | true =>
      simp only [d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d13679 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d13680 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13681 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13682 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d22686 q = 1) (hb : d202307 q = 1) : d207131 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22686, d207131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22686, d207131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro48206 (p : Pattern) (ha : d2039 p = 1) (hb : d202304 p = 1) : d32701 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2014 q = 1) : d2014 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2027 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2039 q = 1) (hb : d202304 q = 1) : d32701 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2039, d202304, d32701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2039, d202304, d32701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro48207 (p : Pattern) (ha : d22687 p = 1) (hb : d202307 p = 1) : d207137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2025 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2040 q = 1) (hb : d202304 q = 1) : d2040 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2041 q = 1) (hb : d202304 q = 1) : d207132 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2041, d207132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48206 q ha hb
    | true =>
      simp only [d2041, d207132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2043 q = 1) (hb : d202304 q = 1) : d2043 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2044 q = 1) (hb : d202304 q = 1) : d207133 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2044, d207133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2044, d207133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2045 q = 1) (hb : d202306 q = 1) : d207134 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2045, d202306, d207134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2045, d202306, d207134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d2030 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2048 q = 1) (hb : d202304 q = 1) : d2048 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2049 q = 1) (hb : d202306 q = 1) : d30103 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2049, d202306, d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d2049, d202306, d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2050 q = 1) (hb : d202306 q = 1) : d207135 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2050, d207135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2050, d207135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2051 q = 1) (hb : d202306 q = 1) : d207136 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2051, d207136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2051, d207136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22687 q = 1) (hb : d202307 q = 1) : d207137 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22687, d202307, d207137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22687, d202307, d207137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro48208 (p : Pattern) (ha : d22694 p = 1) (hb : d202307 p = 1) : d207143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10364 q = 1) (hb : d202307 q = 1) : d207126 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d207126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48203 q ha hb
    | true =>
      simp only [d10364, d207126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10366 q = 1) (hb : d202307 q = 1) : d207127 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d207127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10366, d207127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17153 q = 1) (hb : d202307 q = 1) : d207128 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, d207128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17153, d207128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17154 q = 1) (hb : d202307 q = 1) : d207129 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17154, d207129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17154, d207129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22688 q = 1) (hb : d202307 q = 1) : d207138 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d207138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48207 q ha hb
    | true =>
      simp only [d22688, d207138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22689 q = 1) (hb : d202307 q = 1) : d207139 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d207139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22689, d207139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22690 q = 1) (hb : d202307 q = 1) : d207140 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22690, d207140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22690, d207140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22691 q = 1) (hb : d202307 q = 1) : d207141 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22691, d207141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22691, d207141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22692 q = 1) (hb : d202307 q = 1) : d207142 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22692, d207142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22692, d207142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13678 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48204 q ha hb
    | true =>
      simp only [d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13679 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13680 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13681 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d22693 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22694 q = 1) (hb : d202307 q = 1) : d207143 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22694, d207143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22694, d207143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48209 (p : Pattern) (ha : d10411 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2059 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2076 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2076, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2076, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10407 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10408 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10408, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d10408, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d10409 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10410 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10411 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10411, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10411, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro48210 (p : Pattern) (ha : d22698 p = 1) (hb : d202307 p = 1) : d207150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2025 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5239 q = 1) (hb : d202304 q = 1) : d5239 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5240 q = 1) (hb : d202306 q = 1) : d207147 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5240, d202306, d207147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5240, d202306, d207147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2030 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2048 q = 1) (hb : d202304 q = 1) : d2048 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2049 q = 1) (hb : d202306 q = 1) : d30103 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2049, d202306, d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d2049, d202306, d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5241 q = 1) (hb : d202306 q = 1) : d207148 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5241, d207148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5241, d207148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5242 q = 1) (hb : d202306 q = 1) : d207149 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5242, d207149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5242, d207149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22698 q = 1) (hb : d202307 q = 1) : d207150 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22698, d202307, d207150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22698, d202307, d207150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro48211 (p : Pattern) (ha : d22704 p = 1) (hb : d202307 p = 1) : d207156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22699 q = 1) (hb : d202307 q = 1) : d207151 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22699, d207151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48210 q ha hb
    | true =>
      simp only [d22699, d207151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22700 q = 1) (hb : d202307 q = 1) : d207152 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22700, d207152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22700, d207152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22701 q = 1) (hb : d202307 q = 1) : d207153 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22701, d207153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22701, d207153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22702 q = 1) (hb : d202307 q = 1) : d207154 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22702, d207154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22702, d207154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22703 q = 1) (hb : d202307 q = 1) : d207155 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22703, d207155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22703, d207155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10412 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48209 q ha hb
    | true =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10414 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15555 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15556 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15557 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22704 q = 1) (hb : d202307 q = 1) : d207156 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22704, d207156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22704, d207156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48212 (p : Pattern) (ha : d22710 p = 1) (hb : d202307 p = 1) : d207162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22688 q = 1) (hb : d202307 q = 1) : d207138 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d207138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48207 q ha hb
    | true =>
      simp only [d22688, d207138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22689 q = 1) (hb : d202307 q = 1) : d207139 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d207139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22689, d207139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22690 q = 1) (hb : d202307 q = 1) : d207140 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22690, d207140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22690, d207140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22691 q = 1) (hb : d202307 q = 1) : d207141 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22691, d207141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22691, d207141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22709 q = 1) (hb : d202307 q = 1) : d207161 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22709, d207161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22709, d207161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10412 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48209 q ha hb
    | true =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10414 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15555 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15556 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15557 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22710 q = 1) (hb : d202307 q = 1) : d207162 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22710, d207162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22710, d207162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48213 (p : Pattern) (ha : d22716 p = 1) (hb : d202307 p = 1) : d207168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22695 q = 1) (hb : d202307 q = 1) : d207144 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22695, d207144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48205 q ha hb
    | true =>
      simp only [d22695, d207144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48208 q ha hb
  have h2 (q : Pattern) (ha : d22696 q = 1) (hb : d202307 q = 1) : d207145 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22696, d207145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22696, d207145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22697 q = 1) (hb : d202307 q = 1) : d207146 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22697, d207146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22697, d207146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22705 q = 1) (hb : d202307 q = 1) : d207157 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22705, d207157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48208 q ha hb
    | true =>
      simp only [d22705, d207157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48211 q ha hb
  have h5 (q : Pattern) (ha : d22706 q = 1) (hb : d202307 q = 1) : d207158 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22706, d207158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22706, d207158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22707 q = 1) (hb : d202307 q = 1) : d207159 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22707, d207159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22707, d207159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22708 q = 1) (hb : d202307 q = 1) : d207160 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22708, d207160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22708, d207160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22711 q = 1) (hb : d202307 q = 1) : d207163 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22711, d207163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48208 q ha hb
    | true =>
      simp only [d22711, d207163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48212 q ha hb
  have h9 (q : Pattern) (ha : d22712 q = 1) (hb : d202307 q = 1) : d207164 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22712, d207164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22712, d207164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22713 q = 1) (hb : d202307 q = 1) : d207165 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22713, d207165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22713, d207165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22714 q = 1) (hb : d202307 q = 1) : d207166 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22714, d207166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22714, d207166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d22715 q = 1) (hb : d202307 q = 1) : d207167 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22715, d207167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22715, d207167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22716 q = 1) (hb : d202307 q = 1) : d207168 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22716, d207168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22716, d207168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro48214 (p : Pattern) (ha : d22720 p = 1) (hb : d202307 p = 1) : d207172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22711 q = 1) (hb : d202307 q = 1) : d207163 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22711, d207163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48208 q ha hb
    | true =>
      simp only [d22711, d207163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48212 q ha hb
  have h2 (q : Pattern) (ha : d22712 q = 1) (hb : d202307 q = 1) : d207164 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22712, d207164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22712, d207164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22713 q = 1) (hb : d202307 q = 1) : d207165 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22713, d207165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22713, d207165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22714 q = 1) (hb : d202307 q = 1) : d207166 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22714, d207166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22714, d207166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22719 q = 1) (hb : d202307 q = 1) : d207171 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22719, d207171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22719, d207171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22720 q = 1) (hb : d202307 q = 1) : d207172 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22720, d207172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22720, d207172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48215 (p : Pattern) (ha : d22726 p = 1) (hb : d202307 p = 1) : d207178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d202307 q = 1) : d207169 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48213 q ha hb
    | true =>
      simp only [d22717, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d202307 q = 1) : d207170 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d202307 q = 1) : d207173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48214 q ha hb
    | true =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d202307 q = 1) : d207174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d202307 q = 1) : d207175 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22724 q = 1) (hb : d202307 q = 1) : d207176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22724, d207176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22724, d207176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22725 q = 1) (hb : d202307 q = 1) : d207177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22725, d207177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22725, d207177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22726 q = 1) (hb : d202307 q = 1) : d207178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22726, d207178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22726, d207178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48216 (p : Pattern) (ha : d22730 p = 1) (hb : d202307 p = 1) : d207182 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d202307 q = 1) : d207173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48214 q ha hb
    | true =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d202307 q = 1) : d207174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d202307 q = 1) : d207179 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22728 q = 1) (hb : d202307 q = 1) : d207180 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22728, d207180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22728, d207180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22729 q = 1) (hb : d202307 q = 1) : d207181 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22729, d207181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22729, d207181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22730 q = 1) (hb : d202307 q = 1) : d207182 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22730, d207182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22730, d207182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48217 (p : Pattern) (ha : d22736 p = 1) (hb : d202307 p = 1) : d207188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22731 q = 1) (hb : d202307 q = 1) : d207183 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22731, d207183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48215 q ha hb
    | true =>
      simp only [d22731, d207183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48216 q ha hb
  have h2 (q : Pattern) (ha : d22732 q = 1) (hb : d202307 q = 1) : d207184 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22732, d207184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22732, d207184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22733 q = 1) (hb : d202307 q = 1) : d207185 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22733, d207185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22733, d207185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22734 q = 1) (hb : d202307 q = 1) : d207186 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22734, d207186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22734, d207186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22735 q = 1) (hb : d202307 q = 1) : d207187 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22735, d207187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22735, d207187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22736 q = 1) (hb : d202307 q = 1) : d207188 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22736, d207188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22736, d207188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48218 (p : Pattern) (ha : d22739 p = 1) (hb : d202307 p = 1) : d207191 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d202307 q = 1) : d207169 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48213 q ha hb
    | true =>
      simp only [d22717, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d202307 q = 1) : d207170 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d202307 q = 1) : d207173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48214 q ha hb
    | true =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d202307 q = 1) : d207174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d202307 q = 1) : d207175 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22724 q = 1) (hb : d202307 q = 1) : d207176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22724, d207176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22724, d207176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22725 q = 1) (hb : d202307 q = 1) : d207177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22725, d207177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22725, d207177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22739 q = 1) (hb : d202307 q = 1) : d207191 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22739, d207191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22739, d207191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48219 (p : Pattern) (ha : d22740 p = 1) (hb : d202307 p = 1) : d207192 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d202307 q = 1) : d207173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48214 q ha hb
    | true =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d202307 q = 1) : d207174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d202307 q = 1) : d207179 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22728 q = 1) (hb : d202307 q = 1) : d207180 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22728, d207180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22728, d207180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22729 q = 1) (hb : d202307 q = 1) : d207181 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22729, d207181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22729, d207181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22740 q = 1) (hb : d202307 q = 1) : d207192 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22740, d207192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22740, d207192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48220 (p : Pattern) (ha : d22746 p = 1) (hb : d202307 p = 1) : d207198 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22731 q = 1) (hb : d202307 q = 1) : d207183 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22731, d207183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48215 q ha hb
    | true =>
      simp only [d22731, d207183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48216 q ha hb
  have h2 (q : Pattern) (ha : d22732 q = 1) (hb : d202307 q = 1) : d207184 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22732, d207184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22732, d207184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22733 q = 1) (hb : d202307 q = 1) : d207185 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22733, d207185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22733, d207185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22734 q = 1) (hb : d202307 q = 1) : d207186 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22734, d207186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22734, d207186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22735 q = 1) (hb : d202307 q = 1) : d207187 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22735, d207187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22735, d207187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22741 q = 1) (hb : d202307 q = 1) : d207193 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22741, d207193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48218 q ha hb
    | true =>
      simp only [d22741, d207193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48219 q ha hb
  have h7 (q : Pattern) (ha : d22742 q = 1) (hb : d202307 q = 1) : d207194 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22742, d207194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22742, d207194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22743 q = 1) (hb : d202307 q = 1) : d207195 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22743, d207195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22743, d207195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22744 q = 1) (hb : d202307 q = 1) : d207196 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22744, d207196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22744, d207196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22745 q = 1) (hb : d202307 q = 1) : d207197 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22745, d207197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22745, d207197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22746 q = 1) (hb : d202307 q = 1) : d207198 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22746, d207198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22746, d207198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48221 (p : Pattern) (ha : d22783 p = 1) (hb : d202307 p = 1) : d207232 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22695 q = 1) (hb : d202307 q = 1) : d207144 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22695, d207144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48205 q ha hb
    | true =>
      simp only [d22695, d207144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48208 q ha hb
  have h2 (q : Pattern) (ha : d22696 q = 1) (hb : d202307 q = 1) : d207145 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22696, d207145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22696, d207145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22697 q = 1) (hb : d202307 q = 1) : d207146 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22697, d207146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22697, d207146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22705 q = 1) (hb : d202307 q = 1) : d207157 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22705, d207157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48208 q ha hb
    | true =>
      simp only [d22705, d207157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48211 q ha hb
  have h5 (q : Pattern) (ha : d22706 q = 1) (hb : d202307 q = 1) : d207158 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22706, d207158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22706, d207158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22707 q = 1) (hb : d202307 q = 1) : d207159 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22707, d207159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22707, d207159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22708 q = 1) (hb : d202307 q = 1) : d207160 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22708, d207160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22708, d207160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22781 q = 1) (hb : d202307 q = 1) : d207230 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22781, d207230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22781, d207230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22782 q = 1) (hb : d202307 q = 1) : d207231 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22782, d207231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22782, d207231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22783 q = 1) (hb : d202307 q = 1) : d207232 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22783, d207232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22783, d207232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro48222 (p : Pattern) (ha : d22793 p = 1) (hb : d202307 p = 1) : d207242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22784 q = 1) (hb : d202307 q = 1) : d207233 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22784, d207233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48221 q ha hb
    | true =>
      simp only [d22784, d207233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22785 q = 1) (hb : d202307 q = 1) : d207234 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22785, d207234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22785, d207234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d202307 q = 1) : d207173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48214 q ha hb
    | true =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d202307 q = 1) : d207174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22790 q = 1) (hb : d202307 q = 1) : d207239 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22790, d207239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22790, d207239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22791 q = 1) (hb : d202307 q = 1) : d207240 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22791, d207240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22791, d207240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22792 q = 1) (hb : d202307 q = 1) : d207241 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22792, d207241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22792, d207241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22793 q = 1) (hb : d202307 q = 1) : d207242 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22793, d207242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22793, d207242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48223 (p : Pattern) (ha : d22909 p = 1) (hb : d202307 p = 1) : d207288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22899 q = 1) (hb : d202307 q = 1) : d207278 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22899, d207278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48222 q ha hb
    | true =>
      simp only [d22899, d207278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48216 q ha hb
  have h2 (q : Pattern) (ha : d22900 q = 1) (hb : d202307 q = 1) : d207279 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22900, d207279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22900, d207279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22901 q = 1) (hb : d202307 q = 1) : d207280 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22901, d207280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22901, d207280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22902 q = 1) (hb : d202307 q = 1) : d207281 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22902, d207281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22902, d207281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22903 q = 1) (hb : d202307 q = 1) : d207282 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22903, d207282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22903, d207282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22904 q = 1) (hb : d202307 q = 1) : d207283 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22904, d207283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48216 q ha hb
    | true =>
      simp only [d22904, d207283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22905 q = 1) (hb : d202307 q = 1) : d207284 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22905, d207284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22905, d207284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22906 q = 1) (hb : d202307 q = 1) : d207285 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22906, d207285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22906, d207285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22907 q = 1) (hb : d202307 q = 1) : d207286 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22907, d207286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22907, d207286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22908 q = 1) (hb : d202307 q = 1) : d207287 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22908, d207287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22908, d207287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22909 q = 1) (hb : d202307 q = 1) : d207288 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22909, d207288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22909, d207288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48224 (p : Pattern) (ha : d22915 p = 1) (hb : d202307 p = 1) : d207294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22904 q = 1) (hb : d202307 q = 1) : d207283 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22904, d207283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48216 q ha hb
    | true =>
      simp only [d22904, d207283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22905 q = 1) (hb : d202307 q = 1) : d207284 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22905, d207284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22905, d207284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22906 q = 1) (hb : d202307 q = 1) : d207285 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22906, d207285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22906, d207285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22907 q = 1) (hb : d202307 q = 1) : d207286 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22907, d207286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22907, d207286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22908 q = 1) (hb : d202307 q = 1) : d207287 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22908, d207287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22908, d207287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22910 q = 1) (hb : d202307 q = 1) : d207289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22910, d207289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48219 q ha hb
    | true =>
      simp only [d22910, d207289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22911 q = 1) (hb : d202307 q = 1) : d207290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22911, d207290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22911, d207290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22912 q = 1) (hb : d202307 q = 1) : d207291 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22912, d207291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22912, d207291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22913 q = 1) (hb : d202307 q = 1) : d207292 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22913, d207292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22913, d207292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22914 q = 1) (hb : d202307 q = 1) : d207293 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22914, d207293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22914, d207293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22915 q = 1) (hb : d202307 q = 1) : d207294 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22915, d207294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22915, d207294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48225 (p : Pattern) (ha : d22924 p = 1) (hb : d202307 p = 1) : d207303 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22910 q = 1) (hb : d202307 q = 1) : d207289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22910, d207289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48219 q ha hb
    | true =>
      simp only [d22910, d207289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22911 q = 1) (hb : d202307 q = 1) : d207290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22911, d207290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22911, d207290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22912 q = 1) (hb : d202307 q = 1) : d207291 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22912, d207291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22912, d207291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22913 q = 1) (hb : d202307 q = 1) : d207292 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22913, d207292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22913, d207292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22914 q = 1) (hb : d202307 q = 1) : d207293 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22914, d207293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22914, d207293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22924 q = 1) (hb : d202307 q = 1) : d207303 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22924, d207303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22924, d207303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48226 (p : Pattern) (ha : d22948 p = 1) (hb : d202307 p = 1) : d207327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17376 q = 1) (hb : d202307 q = 1) : d207309 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d207309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17376, d207309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48203 q ha hb
  have h2 (q : Pattern) (ha : d10364 q = 1) (hb : d202307 q = 1) : d207126 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d207126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48203 q ha hb
    | true =>
      simp only [d10364, d207126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17377 q = 1) (hb : d202307 q = 1) : d207310 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d207310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17377, d207310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10366 q = 1) (hb : d202307 q = 1) : d207127 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d207127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10366, d207127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17378 q = 1) (hb : d202307 q = 1) : d207311 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17378, d207311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17378, d207311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17379 q = 1) (hb : d202307 q = 1) : d207312 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17379, d207312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17379, d207312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22943 q = 1) (hb : d202307 q = 1) : d207322 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22943, d207322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22943, d207322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48207 q ha hb
  have h8 (q : Pattern) (ha : d22688 q = 1) (hb : d202307 q = 1) : d207138 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d207138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48207 q ha hb
    | true =>
      simp only [d22688, d207138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22944 q = 1) (hb : d202307 q = 1) : d207323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22944, d207323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22944, d207323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22689 q = 1) (hb : d202307 q = 1) : d207139 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d207139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22689, d207139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22945 q = 1) (hb : d202307 q = 1) : d207324 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22945, d207324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22945, d207324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22946 q = 1) (hb : d202307 q = 1) : d207325 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22946, d207325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22946, d207325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22947 q = 1) (hb : d202307 q = 1) : d207326 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22947, d207326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22947, d207326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13817 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48204 q ha hb
  have h15 (q : Pattern) (ha : d13678 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48204 q ha hb
    | true =>
      simp only [d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d13818 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d13818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13679 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13819 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13820 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d13820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d22937 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d22937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d22948 q = 1) (hb : d202307 q = 1) : d207327 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22948, d207327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22948, d207327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro48227 (p : Pattern) (ha : d22976 p = 1) (hb : d202307 p = 1) : d207355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22943 q = 1) (hb : d202307 q = 1) : d207322 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22943, d207322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22943, d207322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48207 q ha hb
  have h2 (q : Pattern) (ha : d22688 q = 1) (hb : d202307 q = 1) : d207138 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d207138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48207 q ha hb
    | true =>
      simp only [d22688, d207138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22944 q = 1) (hb : d202307 q = 1) : d207323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22944, d207323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22944, d207323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22689 q = 1) (hb : d202307 q = 1) : d207139 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d207139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22689, d207139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22945 q = 1) (hb : d202307 q = 1) : d207324 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22945, d207324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22945, d207324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22946 q = 1) (hb : d202307 q = 1) : d207325 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22946, d207325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22946, d207325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22975 q = 1) (hb : d202307 q = 1) : d207354 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22975, d207354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22975, d207354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15790 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48209 q ha hb
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48209 q ha hb
    | true =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10414 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15792 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15793 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15794 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22976 q = 1) (hb : d202307 q = 1) : d207355 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22976, d207355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22976, d207355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48228 (p : Pattern) (ha : d22982 p = 1) (hb : d202307 p = 1) : d207361 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22977 q = 1) (hb : d202307 q = 1) : d207356 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22977, d207356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48226 q ha hb
    | true =>
      simp only [d22977, d207356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48227 q ha hb
  have h2 (q : Pattern) (ha : d22978 q = 1) (hb : d202307 q = 1) : d207357 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22978, d207357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22978, d207357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22979 q = 1) (hb : d202307 q = 1) : d207358 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22979, d207358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22979, d207358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22980 q = 1) (hb : d202307 q = 1) : d207359 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22980, d207359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22980, d207359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22981 q = 1) (hb : d202307 q = 1) : d207360 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22981, d207360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22981, d207360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22982 q = 1) (hb : d202307 q = 1) : d207361 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22982, d207361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22982, d207361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48229 (p : Pattern) (ha : d23068 p = 1) (hb : d202307 p = 1) : d207388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22983 q = 1) (hb : d202307 q = 1) : d207362 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22983, d207362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48228 q ha hb
    | true =>
      simp only [d22983, d207362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22984 q = 1) (hb : d202307 q = 1) : d207363 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22984, d207363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22984, d207363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23065 q = 1) (hb : d202307 q = 1) : d207385 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23065, d207385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23065, d207385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23066 q = 1) (hb : d202307 q = 1) : d207386 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23066, d207386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23066, d207386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23067 q = 1) (hb : d202307 q = 1) : d207387 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23067, d207387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23067, d207387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23068 q = 1) (hb : d202307 q = 1) : d207388 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23068, d207388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23068, d207388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48230 (p : Pattern) (ha : d23074 p = 1) (hb : d202307 p = 1) : d207394 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23069 q = 1) (hb : d202307 q = 1) : d207389 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23069, d207389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48229 q ha hb
    | true =>
      simp only [d23069, d207389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23070 q = 1) (hb : d202307 q = 1) : d207390 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23070, d207390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23070, d207390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23071 q = 1) (hb : d202307 q = 1) : d207391 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23071, d207391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23071, d207391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23072 q = 1) (hb : d202307 q = 1) : d207392 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23072, d207392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23072, d207392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23073 q = 1) (hb : d202307 q = 1) : d207393 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23073, d207393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23073, d207393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23074 q = 1) (hb : d202307 q = 1) : d207394 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23074, d207394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23074, d207394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48231 (p : Pattern) (ha : d22751 p = 1) (hb : d202307 p = 1) : d207203 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d202307 q = 1) : d207169 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48213 q ha hb
    | true =>
      simp only [d22717, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d202307 q = 1) : d207170 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d202307 q = 1) : d207173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48214 q ha hb
    | true =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d202307 q = 1) : d207174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d202307 q = 1) : d207175 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22724 q = 1) (hb : d202307 q = 1) : d207176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22724, d207176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22724, d207176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22750 q = 1) (hb : d202307 q = 1) : d207202 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22750, d207202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22750, d207202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22751 q = 1) (hb : d202307 q = 1) : d207203 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22751, d207203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22751, d207203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48232 (p : Pattern) (ha : d22753 p = 1) (hb : d202307 p = 1) : d207205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d202307 q = 1) : d207173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48214 q ha hb
    | true =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d202307 q = 1) : d207174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d202307 q = 1) : d207179 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22728 q = 1) (hb : d202307 q = 1) : d207180 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22728, d207180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22728, d207180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22752 q = 1) (hb : d202307 q = 1) : d207204 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22752, d207204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22752, d207204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22753 q = 1) (hb : d202307 q = 1) : d207205 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22753, d207205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22753, d207205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48233 (p : Pattern) (ha : d22760 p = 1) (hb : d202307 p = 1) : d207212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d202307 q = 1) : d207169 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48213 q ha hb
    | true =>
      simp only [d22717, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d202307 q = 1) : d207170 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d202307 q = 1) : d207173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48214 q ha hb
    | true =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d202307 q = 1) : d207174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d202307 q = 1) : d207175 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22758 q = 1) (hb : d202307 q = 1) : d207210 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22758, d207210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22758, d207210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22759 q = 1) (hb : d202307 q = 1) : d207211 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22759, d207211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22759, d207211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22760 q = 1) (hb : d202307 q = 1) : d207212 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22760, d207212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22760, d207212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48234 (p : Pattern) (ha : d22763 p = 1) (hb : d202307 p = 1) : d207215 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d202307 q = 1) : d207173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48214 q ha hb
    | true =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d202307 q = 1) : d207174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d202307 q = 1) : d207179 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22761 q = 1) (hb : d202307 q = 1) : d207213 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22761, d207213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22761, d207213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22762 q = 1) (hb : d202307 q = 1) : d207214 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22762, d207214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22762, d207214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22763 q = 1) (hb : d202307 q = 1) : d207215 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22763, d207215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22763, d207215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48235 (p : Pattern) (ha : d22768 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10343 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48197 q ha hb
    | true =>
      simp only [d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10345 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17225 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17226 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22767 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10353 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48198 q ha hb
    | true =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10355 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13675 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13676 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17228 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22768 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48236 (p : Pattern) (ha : d22772 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10353 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48198 q ha hb
    | true =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10355 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13675 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13676 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13678 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48204 q ha hb
    | true =>
      simp only [d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13679 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13680 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13681 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13682 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22693 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22772 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48237 (p : Pattern) (ha : d22778 p = 1) (hb : d202307 p = 1) : d207227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22769 q = 1) (hb : d202307 q = 1) : d207219 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22769, d207219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48235 q ha hb
    | true =>
      simp only [d22769, d207219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48205 q ha hb
  have h2 (q : Pattern) (ha : d22770 q = 1) (hb : d202307 q = 1) : d207220 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22770, d207220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22770, d207220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22771 q = 1) (hb : d202307 q = 1) : d207221 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22771, d207221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22771, d207221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22773 q = 1) (hb : d202307 q = 1) : d207222 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22773, d207222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48205 q ha hb
    | true =>
      simp only [d22773, d207222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48236 q ha hb
  have h5 (q : Pattern) (ha : d22774 q = 1) (hb : d202307 q = 1) : d207223 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22774, d207223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22774, d207223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22775 q = 1) (hb : d202307 q = 1) : d207224 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22775, d207224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22775, d207224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22776 q = 1) (hb : d202307 q = 1) : d207225 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22776, d207225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22776, d207225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22695 q = 1) (hb : d202307 q = 1) : d207144 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22695, d207144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48205 q ha hb
    | true =>
      simp only [d22695, d207144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48208 q ha hb
  have h9 (q : Pattern) (ha : d22696 q = 1) (hb : d202307 q = 1) : d207145 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22696, d207145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22696, d207145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22697 q = 1) (hb : d202307 q = 1) : d207146 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22697, d207146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22697, d207146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22705 q = 1) (hb : d202307 q = 1) : d207157 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22705, d207157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48208 q ha hb
    | true =>
      simp only [d22705, d207157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48211 q ha hb
  have h12 (q : Pattern) (ha : d22706 q = 1) (hb : d202307 q = 1) : d207158 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22706, d207158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22706, d207158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22707 q = 1) (hb : d202307 q = 1) : d207159 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22707, d207159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22707, d207159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22708 q = 1) (hb : d202307 q = 1) : d207160 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22708, d207160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22708, d207160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22777 q = 1) (hb : d202307 q = 1) : d207226 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22777, d207226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22777, d207226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22778 q = 1) (hb : d202307 q = 1) : d207227 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22778, d207227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d22778, d207227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro48238 (p : Pattern) (ha : d22789 p = 1) (hb : d202307 p = 1) : d207238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22779 q = 1) (hb : d202307 q = 1) : d207228 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22779, d207228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48237 q ha hb
    | true =>
      simp only [d22779, d207228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22780 q = 1) (hb : d202307 q = 1) : d207229 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22780, d207229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22780, d207229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22784 q = 1) (hb : d202307 q = 1) : d207233 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22784, d207233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48221 q ha hb
    | true =>
      simp only [d22784, d207233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22785 q = 1) (hb : d202307 q = 1) : d207234 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22785, d207234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22785, d207234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22786 q = 1) (hb : d202307 q = 1) : d207235 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22786, d207235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22786, d207235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22787 q = 1) (hb : d202307 q = 1) : d207236 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22787, d207236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22787, d207236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22788 q = 1) (hb : d202307 q = 1) : d207237 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22788, d207237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22788, d207237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22789 q = 1) (hb : d202307 q = 1) : d207238 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22789, d207238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22789, d207238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48239 (p : Pattern) (ha : d22854 p = 1) (hb : d202307 p = 1) : d207162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22688 q = 1) (hb : d202307 q = 1) : d207138 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d207138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48207 q ha hb
    | true =>
      simp only [d22688, d207138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22689 q = 1) (hb : d202307 q = 1) : d207139 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d207139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22689, d207139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22690 q = 1) (hb : d202307 q = 1) : d207140 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22690, d207140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22690, d207140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22691 q = 1) (hb : d202307 q = 1) : d207141 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22691, d207141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22691, d207141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22709 q = 1) (hb : d202307 q = 1) : d207161 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22709, d207161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22709, d207161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22854 q = 1) (hb : d202307 q = 1) : d207162 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22854, d207162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22854, d207162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48240 (p : Pattern) (ha : d22860 p = 1) (hb : d202307 p = 1) : d207168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22695 q = 1) (hb : d202307 q = 1) : d207144 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22695, d207144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48205 q ha hb
    | true =>
      simp only [d22695, d207144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48208 q ha hb
  have h2 (q : Pattern) (ha : d22696 q = 1) (hb : d202307 q = 1) : d207145 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22696, d207145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22696, d207145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22697 q = 1) (hb : d202307 q = 1) : d207146 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22697, d207146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22697, d207146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22705 q = 1) (hb : d202307 q = 1) : d207157 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22705, d207157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48208 q ha hb
    | true =>
      simp only [d22705, d207157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48211 q ha hb
  have h5 (q : Pattern) (ha : d22706 q = 1) (hb : d202307 q = 1) : d207158 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22706, d207158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22706, d207158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22707 q = 1) (hb : d202307 q = 1) : d207159 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22707, d207159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22707, d207159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22708 q = 1) (hb : d202307 q = 1) : d207160 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22708, d207160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22708, d207160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22855 q = 1) (hb : d202307 q = 1) : d207163 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22855, d207163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48208 q ha hb
    | true =>
      simp only [d22855, d207163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48239 q ha hb
  have h9 (q : Pattern) (ha : d22856 q = 1) (hb : d202307 q = 1) : d207164 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22856, d207164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22856, d207164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22857 q = 1) (hb : d202307 q = 1) : d207165 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22857, d207165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22857, d207165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22858 q = 1) (hb : d202307 q = 1) : d207166 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22858, d207166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22858, d207166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d22859 q = 1) (hb : d202307 q = 1) : d207167 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22859, d207167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22859, d207167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22860 q = 1) (hb : d202307 q = 1) : d207168 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22860, d207168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22860, d207168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro48241 (p : Pattern) (ha : d22866 p = 1) (hb : d202307 p = 1) : d207248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22861 q = 1) (hb : d202307 q = 1) : d207169 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22861, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48240 q ha hb
    | true =>
      simp only [d22861, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22862 q = 1) (hb : d202307 q = 1) : d207170 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22862, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22862, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22863 q = 1) (hb : d202307 q = 1) : d207245 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22863, d207245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22863, d207245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22864 q = 1) (hb : d202307 q = 1) : d207246 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22864, d207246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22864, d207246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22865 q = 1) (hb : d202307 q = 1) : d207247 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22865, d207247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22865, d207247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22866 q = 1) (hb : d202307 q = 1) : d207248 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22866, d207248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22866, d207248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48242 (p : Pattern) (ha : d150244 p = 1) (hb : d202307 p = 1) : d207254 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22754 q = 1) (hb : d202307 q = 1) : d207206 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22754, d207206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48231 q ha hb
    | true =>
      simp only [d22754, d207206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48232 q ha hb
  have h2 (q : Pattern) (ha : d22755 q = 1) (hb : d202307 q = 1) : d207207 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22755, d207207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22755, d207207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22756 q = 1) (hb : d202307 q = 1) : d207208 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22756, d207208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22756, d207208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22757 q = 1) (hb : d202307 q = 1) : d207209 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22757, d207209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22757, d207209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22764 q = 1) (hb : d202307 q = 1) : d207216 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22764, d207216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48233 q ha hb
    | true =>
      simp only [d22764, d207216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48234 q ha hb
  have h6 (q : Pattern) (ha : d22765 q = 1) (hb : d202307 q = 1) : d207217 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22765, d207217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22765, d207217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22766 q = 1) (hb : d202307 q = 1) : d207218 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22766, d207218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22766, d207218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22794 q = 1) (hb : d202307 q = 1) : d207243 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22794, d207243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48238 q ha hb
    | true =>
      simp only [d22794, d207243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48222 q ha hb
  have h9 (q : Pattern) (ha : d150240 q = 1) (hb : d202307 q = 1) : d207244 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150240, d207244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150240, d207244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d22867 q = 1) (hb : d202307 q = 1) : d207249 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22867, d207249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48241 q ha hb
    | true =>
      simp only [d22867, d207249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22868 q = 1) (hb : d202307 q = 1) : d207250 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22868, d207250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22868, d207250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150241 q = 1) (hb : d202307 q = 1) : d207251 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150241, d207251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150241, d207251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150242 q = 1) (hb : d202307 q = 1) : d207252 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150242, d207252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150242, d207252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150243 q = 1) (hb : d202307 q = 1) : d207253 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150243, d207253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150243, d207253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150244 q = 1) (hb : d202307 q = 1) : d207254 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150244, d207254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150244, d207254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48243 (p : Pattern) (ha : d22873 p = 1) (hb : d202307 p = 1) : d207255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d202307 q = 1) : d207169 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48213 q ha hb
    | true =>
      simp only [d22717, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d202307 q = 1) : d207170 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d202307 q = 1) : d207173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48214 q ha hb
    | true =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d202307 q = 1) : d207174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d202307 q = 1) : d207175 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22724 q = 1) (hb : d202307 q = 1) : d207176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22724, d207176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22724, d207176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22750 q = 1) (hb : d202307 q = 1) : d207202 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22750, d207202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22750, d207202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22873 q = 1) (hb : d202307 q = 1) : d207255 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22873, d207255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22873, d207255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48244 (p : Pattern) (ha : d22874 p = 1) (hb : d202307 p = 1) : d207256 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d202307 q = 1) : d207173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48214 q ha hb
    | true =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d202307 q = 1) : d207174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d202307 q = 1) : d207179 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22728 q = 1) (hb : d202307 q = 1) : d207180 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22728, d207180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22728, d207180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22752 q = 1) (hb : d202307 q = 1) : d207204 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22752, d207204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22752, d207204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22874 q = 1) (hb : d202307 q = 1) : d207256 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22874, d207256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22874, d207256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48245 (p : Pattern) (ha : d22879 p = 1) (hb : d202307 p = 1) : d207261 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d202307 q = 1) : d207169 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48213 q ha hb
    | true =>
      simp only [d22717, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d202307 q = 1) : d207170 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d202307 q = 1) : d207173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48214 q ha hb
    | true =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d202307 q = 1) : d207174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d202307 q = 1) : d207175 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22758 q = 1) (hb : d202307 q = 1) : d207210 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22758, d207210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22758, d207210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22759 q = 1) (hb : d202307 q = 1) : d207211 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22759, d207211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22759, d207211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22879 q = 1) (hb : d202307 q = 1) : d207261 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22879, d207261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22879, d207261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48246 (p : Pattern) (ha : d22880 p = 1) (hb : d202307 p = 1) : d207262 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d202307 q = 1) : d207173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48214 q ha hb
    | true =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d202307 q = 1) : d207174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d202307 q = 1) : d207179 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22761 q = 1) (hb : d202307 q = 1) : d207213 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22761, d207213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22761, d207213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22762 q = 1) (hb : d202307 q = 1) : d207214 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22762, d207214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22762, d207214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22880 q = 1) (hb : d202307 q = 1) : d207262 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22880, d207262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22880, d207262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48247 (p : Pattern) (ha : d22884 p = 1) (hb : d202307 p = 1) : d207266 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22779 q = 1) (hb : d202307 q = 1) : d207228 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22779, d207228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48237 q ha hb
    | true =>
      simp only [d22779, d207228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22780 q = 1) (hb : d202307 q = 1) : d207229 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22780, d207229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22780, d207229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22784 q = 1) (hb : d202307 q = 1) : d207233 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22784, d207233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48221 q ha hb
    | true =>
      simp only [d22784, d207233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22785 q = 1) (hb : d202307 q = 1) : d207234 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22785, d207234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22785, d207234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22786 q = 1) (hb : d202307 q = 1) : d207235 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22786, d207235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22786, d207235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22787 q = 1) (hb : d202307 q = 1) : d207236 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22787, d207236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22787, d207236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22788 q = 1) (hb : d202307 q = 1) : d207237 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22788, d207237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22788, d207237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22884 q = 1) (hb : d202307 q = 1) : d207266 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22884, d207266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22884, d207266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48248 (p : Pattern) (ha : d22885 p = 1) (hb : d202307 p = 1) : d207267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22784 q = 1) (hb : d202307 q = 1) : d207233 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22784, d207233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48221 q ha hb
    | true =>
      simp only [d22784, d207233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22785 q = 1) (hb : d202307 q = 1) : d207234 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22785, d207234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22785, d207234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d202307 q = 1) : d207173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48214 q ha hb
    | true =>
      simp only [d22721, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d202307 q = 1) : d207174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22790 q = 1) (hb : d202307 q = 1) : d207239 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22790, d207239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22790, d207239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22791 q = 1) (hb : d202307 q = 1) : d207240 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22791, d207240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22791, d207240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22792 q = 1) (hb : d202307 q = 1) : d207241 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22792, d207241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22792, d207241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22885 q = 1) (hb : d202307 q = 1) : d207267 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22885, d207267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22885, d207267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48249 (p : Pattern) (ha : d22891 p = 1) (hb : d202307 p = 1) : d207270 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22861 q = 1) (hb : d202307 q = 1) : d207169 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22861, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48240 q ha hb
    | true =>
      simp only [d22861, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22862 q = 1) (hb : d202307 q = 1) : d207170 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22862, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22862, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22863 q = 1) (hb : d202307 q = 1) : d207245 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22863, d207245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22863, d207245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22864 q = 1) (hb : d202307 q = 1) : d207246 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22864, d207246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22864, d207246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22865 q = 1) (hb : d202307 q = 1) : d207247 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22865, d207247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22865, d207247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22891 q = 1) (hb : d202307 q = 1) : d207270 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22891, d207270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22891, d207270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
