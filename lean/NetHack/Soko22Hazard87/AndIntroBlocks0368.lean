import NetHack.Soko22Hazard87.AndIntroBlocks0367
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro92000 (p : Pattern) (ha : d336346 p = 1) (hb : d337338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336318 q = 1) (hb : d337310 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336318, d337310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91995 q ha hb
    | true =>
      simp only [d336318, d337310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91977 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d336229 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d336319 q = 1) (hb : d337311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336319, d337311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336319, d337311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d336321 q = 1) (hb : d337313 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336321, d337313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91996 q ha hb
    | true =>
      simp only [d336321, d337313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336322 q = 1) (hb : d337314 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336322, d337314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336322, d337314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336323 q = 1) (hb : d337315 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336323, d337315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336323, d337315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336344 q = 1) (hb : d337336 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336344, d337336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336344, d337336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336345 q = 1) (hb : d337337 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336345, d337337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336345, d337337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d336346 q = 1) (hb : d337338 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336346, d337338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336346, d337338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro92001 (p : Pattern) (ha : d336348 p = 1) (hb : d337340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336334 q = 1) (hb : d337326 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336334, d337326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91978 q ha hb
    | true =>
      simp only [d336334, d337326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336335 q = 1) (hb : d337327 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336335, d337327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336335, d337327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336336 q = 1) (hb : d337328 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336336, d337328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336336, d337328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336337 q = 1) (hb : d337329 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336337, d337329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336337, d337329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336338 q = 1) (hb : d337330 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336338, d337330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336338, d337330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336348 q = 1) (hb : d337340 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336348, d337340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336348, d337340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92002 (p : Pattern) (ha : d336369 p = 1) (hb : d337360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336094 q = 1) (hb : d337346 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336094, d337346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336094, d337346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91963 q ha hb
  have h2 (q : Pattern) (ha : d336007 q = 1) (hb : d337163 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336007, d337163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91963 q ha hb
    | true =>
      simp only [d336007, d337163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336095 q = 1) (hb : d337347 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336095, d337347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336095, d337347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336008 q = 1) (hb : d337164 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336008, d337164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336008, d337164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336096 q = 1) (hb : d337348 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336096, d337348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336096, d337348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336097 q = 1) (hb : d337349 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336097, d337349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336097, d337349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336098 q = 1) (hb : d337350 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336098, d337350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336098, d337350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91964 q ha hb
  have h8 (q : Pattern) (ha : d336012 q = 1) (hb : d337168 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336012, d337168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91964 q ha hb
    | true =>
      simp only [d336012, d337168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d336099 q = 1) (hb : d337351 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336099, d337351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336099, d337351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336013 q = 1) (hb : d337169 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336013, d337169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d336013, d337169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d336100 q = 1) (hb : d337352 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336100, d337352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d336100, d337352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d336101 q = 1) (hb : d337353 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336101, d337353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d336101, d337353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d336102 q = 1) (hb : d337354 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336102, d337354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336102, d337354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d336364 q = 1) (hb : d337355 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336364, d337355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336364, d337355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91965 q ha hb
  have h15 (q : Pattern) (ha : d336184 q = 1) (hb : d337177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336184, d337177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91965 q ha hb
    | true =>
      simp only [d336184, d337177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d336365 q = 1) (hb : d337356 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336365, d337356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d336365, d337356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d336185 q = 1) (hb : d337178 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336185, d337178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d336185, d337178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d336366 q = 1) (hb : d337357 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336366, d337357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d336366, d337357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d336367 q = 1) (hb : d337358 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336367, d337358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d336367, d337358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d336368 q = 1) (hb : d337359 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336368, d337359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336368, d337359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d336369 q = 1) (hb : d337360 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336369, d337360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d336369, d337360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro92003 (p : Pattern) (ha : d336374 p = 1) (hb : d337365 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336364 q = 1) (hb : d337355 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336364, d337355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336364, d337355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91965 q ha hb
  have h2 (q : Pattern) (ha : d336184 q = 1) (hb : d337177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336184, d337177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91965 q ha hb
    | true =>
      simp only [d336184, d337177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336365 q = 1) (hb : d337356 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336365, d337356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336365, d337356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336185 q = 1) (hb : d337178 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336185, d337178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336185, d337178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336366 q = 1) (hb : d337357 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336366, d337357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336366, d337357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336367 q = 1) (hb : d337358 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336367, d337358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336367, d337358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336368 q = 1) (hb : d337359 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336368, d337359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336368, d337359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336373 q = 1) (hb : d337364 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336373, d337364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336373, d337364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d336374 q = 1) (hb : d337365 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336374, d337365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336374, d337365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro92004 (p : Pattern) (ha : d336380 p = 1) (hb : d337379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d335881 q = 1) (hb : d337370 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335881, d337370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d335881, d337370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91968 q ha hb
  have h2 (q : Pattern) (ha : d335808 q = 1) (hb : d337187 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335808, d337187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91968 q ha hb
    | true =>
      simp only [d335808, d337187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d335882 q = 1) (hb : d337371 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335882, d337371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d335882, d337371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d335809 q = 1) (hb : d337188 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335809, d337188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d335809, d337188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d335883 q = 1) (hb : d337372 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335883, d337372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d335883, d337372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d335884 q = 1) (hb : d337373 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335884, d337373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d335884, d337373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d335741 q = 1) (hb : d337374 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335741, d337374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d335741, d337374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91967 q ha hb
  have h8 (q : Pattern) (ha : d335687 q = 1) (hb : d337192 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335687, d337192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91967 q ha hb
    | true =>
      simp only [d335687, d337192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d335742 q = 1) (hb : d337375 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335742, d337375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d335742, d337375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d335688 q = 1) (hb : d337193 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335688, d337193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d335688, d337193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d335743 q = 1) (hb : d337376 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335743, d337376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d335743, d337376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d335744 q = 1) (hb : d337377 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335744, d337377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d335744, d337377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d336379 q = 1) (hb : d337378 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336379, d337378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336379, d337378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d336364 q = 1) (hb : d337355 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336364, d337355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336364, d337355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91965 q ha hb
  have h15 (q : Pattern) (ha : d336184 q = 1) (hb : d337177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336184, d337177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91965 q ha hb
    | true =>
      simp only [d336184, d337177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d336365 q = 1) (hb : d337356 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336365, d337356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d336365, d337356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d336185 q = 1) (hb : d337178 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336185, d337178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d336185, d337178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d336366 q = 1) (hb : d337357 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336366, d337357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d336366, d337357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d336367 q = 1) (hb : d337358 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336367, d337358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d336367, d337358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d336373 q = 1) (hb : d337364 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336373, d337364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d336373, d337364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d336380 q = 1) (hb : d337379 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336380, d337379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d336380, d337379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro92005 (p : Pattern) (ha : d336385 p = 1) (hb : d337384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d335741 q = 1) (hb : d337374 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335741, d337374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d335741, d337374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91967 q ha hb
  have h2 (q : Pattern) (ha : d335687 q = 1) (hb : d337192 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335687, d337192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91967 q ha hb
    | true =>
      simp only [d335687, d337192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d335742 q = 1) (hb : d337375 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335742, d337375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d335742, d337375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d335688 q = 1) (hb : d337193 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335688, d337193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d335688, d337193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d335743 q = 1) (hb : d337376 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335743, d337376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d335743, d337376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d335744 q = 1) (hb : d337377 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335744, d337377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d335744, d337377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336384 q = 1) (hb : d337383 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336384, d337383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336384, d337383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d1406 q = 1) (hb : d335621 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1406, d335621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1406, d335621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91970 q ha hb
  have h9 (q : Pattern) (ha : d1136 q = 1) (hb : d335580 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1136, d335580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91970 q ha hb
    | true =>
      simp only [d1136, d335580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1407 q = 1) (hb : d335622 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1407, d335622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1407, d335622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1137 q = 1) (hb : d335581 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1137, d335581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1137, d335581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1408 q = 1) (hb : d335623 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1408, d335623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1408, d335623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1409 q = 1) (hb : d335624 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1409, d335624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1409, d335624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d1410 q = 1) (hb : d335625 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1410, d335625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1410, d335625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d336385 q = 1) (hb : d337384 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336385, d337384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336385, d337384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro92006 (p : Pattern) (ha : d336391 p = 1) (hb : d337390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d336363 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d336370 q = 1) (hb : d337361 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336370, d337361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336370, d337361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92002 q ha hb
  have h3 (q : Pattern) (ha : d336371 q = 1) (hb : d337362 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336371, d337362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336371, d337362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336372 q = 1) (hb : d337363 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336372, d337363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336372, d337363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336375 q = 1) (hb : d337366 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336375, d337366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92002 q ha hb
    | true =>
      simp only [d336375, d337366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92003 q ha hb
  have h6 (q : Pattern) (ha : d336376 q = 1) (hb : d337367 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336376, d337367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336376, d337367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336377 q = 1) (hb : d337368 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336377, d337368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336377, d337368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336378 q = 1) (hb : d337369 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336378, d337369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336378, d337369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d336381 q = 1) (hb : d337380 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336381, d337380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92002 q ha hb
    | true =>
      simp only [d336381, d337380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92004 q ha hb
  have h10 (q : Pattern) (ha : d336382 q = 1) (hb : d337381 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336382, d337381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336382, d337381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d336383 q = 1) (hb : d337382 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336383, d337382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336383, d337382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d336386 q = 1) (hb : d337385 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336386, d337385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92004 q ha hb
    | true =>
      simp only [d336386, d337385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92005 q ha hb
  have h13 (q : Pattern) (ha : d336387 q = 1) (hb : d337386 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336387, d337386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336387, d337386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d336388 q = 1) (hb : d337387 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336388, d337387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336388, d337387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d336389 q = 1) (hb : d337388 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336389, d337388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d336389, d337388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d336390 q = 1) (hb : d337389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d336390, d337389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d336390, d337389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d336391 q = 1) (hb : d337390 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d336391, d337390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d336391, d337390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro92007 (p : Pattern) (ha : d336396 p = 1) (hb : d337395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336381 q = 1) (hb : d337380 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336381, d337380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92002 q ha hb
    | true =>
      simp only [d336381, d337380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92004 q ha hb
  have h2 (q : Pattern) (ha : d336382 q = 1) (hb : d337381 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336382, d337381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336382, d337381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336383 q = 1) (hb : d337382 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336383, d337382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336383, d337382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336386 q = 1) (hb : d337385 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336386, d337385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92004 q ha hb
    | true =>
      simp only [d336386, d337385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92005 q ha hb
  have h5 (q : Pattern) (ha : d336387 q = 1) (hb : d337386 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336387, d337386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336387, d337386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336388 q = 1) (hb : d337387 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336388, d337387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336388, d337387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336389 q = 1) (hb : d337388 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336389, d337388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336389, d337388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336394 q = 1) (hb : d337393 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336394, d337393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336394, d337393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d336395 q = 1) (hb : d337394 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d336395, d337394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336395, d337394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336396 q = 1) (hb : d337395 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d336396, d337395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d336396, d337395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro92008 (p : Pattern) (ha : d336402 p = 1) (hb : d337401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336392 q = 1) (hb : d337391 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336392, d337391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92006 q ha hb
    | true =>
      simp only [d336392, d337391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336393 q = 1) (hb : d337392 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336393, d337392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336393, d337392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336397 q = 1) (hb : d337396 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336397, d337396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92007 q ha hb
    | true =>
      simp only [d336397, d337396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336398 q = 1) (hb : d337397 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336398, d337397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336398, d337397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336399 q = 1) (hb : d337398 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336399, d337398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336399, d337398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336400 q = 1) (hb : d337399 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336400, d337399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336400, d337399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336401 q = 1) (hb : d337400 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336401, d337400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336401, d337400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336402 q = 1) (hb : d337401 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336402, d337401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336402, d337401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro92009 (p : Pattern) (ha : d336404 p = 1) (hb : d337403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336386 q = 1) (hb : d337385 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336386, d337385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92004 q ha hb
    | true =>
      simp only [d336386, d337385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92005 q ha hb
  have h2 (q : Pattern) (ha : d336387 q = 1) (hb : d337386 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336387, d337386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336387, d337386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336388 q = 1) (hb : d337387 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336388, d337387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336388, d337387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336394 q = 1) (hb : d337393 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336394, d337393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336394, d337393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336403 q = 1) (hb : d337402 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d336403, d337402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336403, d337402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336404 q = 1) (hb : d337403 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d336404, d337403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336404, d337403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92010 (p : Pattern) (ha : d336410 p = 1) (hb : d337409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336397 q = 1) (hb : d337396 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336397, d337396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92007 q ha hb
    | true =>
      simp only [d336397, d337396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336398 q = 1) (hb : d337397 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336398, d337397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336398, d337397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336405 q = 1) (hb : d337404 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336405, d337404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92009 q ha hb
    | true =>
      simp only [d336405, d337404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336406 q = 1) (hb : d337405 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336406, d337405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336406, d337405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336407 q = 1) (hb : d337406 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336407, d337406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336407, d337406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336408 q = 1) (hb : d337407 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336408, d337407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336408, d337407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336409 q = 1) (hb : d337408 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336409, d337408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336409, d337408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336410 q = 1) (hb : d337409 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336410, d337409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336410, d337409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro92011 (p : Pattern) (ha : d336418 p = 1) (hb : d337412 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d335741 q = 1) (hb : d337374 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335741, d337374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d335741, d337374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91967 q ha hb
  have h2 (q : Pattern) (ha : d335687 q = 1) (hb : d337192 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335687, d337192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91967 q ha hb
    | true =>
      simp only [d335687, d337192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d335742 q = 1) (hb : d337375 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335742, d337375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d335742, d337375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d335688 q = 1) (hb : d337193 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335688, d337193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d335688, d337193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d335743 q = 1) (hb : d337376 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335743, d337376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d335743, d337376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d335744 q = 1) (hb : d337377 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335744, d337377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d335744, d337377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336384 q = 1) (hb : d337383 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336384, d337383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336384, d337383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336418 q = 1) (hb : d337412 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336418, d337412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336418, d337412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro92012 (p : Pattern) (ha : d336424 p = 1) (hb : d337418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336381 q = 1) (hb : d337380 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336381, d337380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92002 q ha hb
    | true =>
      simp only [d336381, d337380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92004 q ha hb
  have h2 (q : Pattern) (ha : d336382 q = 1) (hb : d337381 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336382, d337381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336382, d337381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336383 q = 1) (hb : d337382 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336383, d337382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336383, d337382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336386 q = 1) (hb : d337385 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336386, d337385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92004 q ha hb
    | true =>
      simp only [d336386, d337385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92005 q ha hb
  have h5 (q : Pattern) (ha : d336387 q = 1) (hb : d337386 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336387, d337386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336387, d337386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336388 q = 1) (hb : d337387 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336388, d337387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336388, d337387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336389 q = 1) (hb : d337388 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336389, d337388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336389, d337388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336419 q = 1) (hb : d337413 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336419, d337413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92004 q ha hb
    | true =>
      simp only [d336419, d337413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92011 q ha hb
  have h9 (q : Pattern) (ha : d336420 q = 1) (hb : d337414 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336420, d337414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336420, d337414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336421 q = 1) (hb : d337415 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336421, d337415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336421, d337415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d336422 q = 1) (hb : d337416 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336422, d337416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336422, d337416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d336423 q = 1) (hb : d337417 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d336423, d337417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336423, d337417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d336424 q = 1) (hb : d337418 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d336424, d337418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d336424, d337418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro92013 (p : Pattern) (ha : d336430 p = 1) (hb : d337424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336425 q = 1) (hb : d337419 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336425, d337419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92012 q ha hb
    | true =>
      simp only [d336425, d337419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336426 q = 1) (hb : d337420 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336426, d337420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336426, d337420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336427 q = 1) (hb : d337421 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336427, d337421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336427, d337421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336428 q = 1) (hb : d337422 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336428, d337422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336428, d337422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336429 q = 1) (hb : d337423 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336429, d337423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336429, d337423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336430 q = 1) (hb : d337424 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336430, d337424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336430, d337424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92014 (p : Pattern) (ha : d336436 p = 1) (hb : d337430 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336411 q = 1) (hb : d337410 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336411, d337410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92008 q ha hb
    | true =>
      simp only [d336411, d337410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92010 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d336416 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d336417 q = 1) (hb : d337411 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336417, d337411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336417, d337411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d336431 q = 1) (hb : d337425 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336431, d337425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92013 q ha hb
    | true =>
      simp only [d336431, d337425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336432 q = 1) (hb : d337426 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336432, d337426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336432, d337426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336433 q = 1) (hb : d337427 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336433, d337427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336433, d337427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336434 q = 1) (hb : d337428 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336434, d337428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336434, d337428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336435 q = 1) (hb : d337429 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336435, d337429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336435, d337429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d336436 q = 1) (hb : d337430 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336436, d337430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336436, d337430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro92015 (p : Pattern) (ha : d336415 p = 1) (hb : d337435 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336405 q = 1) (hb : d337404 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336405, d337404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92009 q ha hb
    | true =>
      simp only [d336405, d337404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336406 q = 1) (hb : d337405 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336406, d337405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336406, d337405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336412 q = 1) (hb : d337432 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336412, d337432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336412, d337432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336413 q = 1) (hb : d337433 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336413, d337433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336413, d337433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336414 q = 1) (hb : d337434 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336414, d337434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336414, d337434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336415 q = 1) (hb : d337435 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336415, d337435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336415, d337435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92016 (p : Pattern) (ha : d336443 p = 1) (hb : d337441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336438 q = 1) (hb : d337436 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336438, d337436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92015 q ha hb
    | true =>
      simp only [d336438, d337436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336439 q = 1) (hb : d337437 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336439, d337437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336439, d337437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336440 q = 1) (hb : d337438 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336440, d337438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336440, d337438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336441 q = 1) (hb : d337439 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336441, d337439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336441, d337439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336442 q = 1) (hb : d337440 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336442, d337440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336442, d337440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336443 q = 1) (hb : d337441 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336443, d337441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336443, d337441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92017 (p : Pattern) (ha : d336449 p = 1) (hb : d337447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336225 q = 1) (hb : d337231 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336225, d337231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336225, d337231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91976 q ha hb
  have h2 (q : Pattern) (ha : d336226 q = 1) (hb : d337232 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336226, d337232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336226, d337232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336235 q = 1) (hb : d337241 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336235, d337241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91976 q ha hb
    | true =>
      simp only [d336235, d337241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91979 q ha hb
  have h4 (q : Pattern) (ha : d336236 q = 1) (hb : d337242 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336236, d337242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336236, d337242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336237 q = 1) (hb : d337243 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d336237, d337243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336237, d337243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336327 q = 1) (hb : d337319 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336327, d337319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91990 q ha hb
    | true =>
      simp only [d336327, d337319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91997 q ha hb
  have h7 (q : Pattern) (ha : d336340 q = 1) (hb : d337332 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336340, d337332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91998 q ha hb
    | true =>
      simp only [d336340, d337332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91999 q ha hb
  have h8 (q : Pattern) (ha : d336341 q = 1) (hb : d337333 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336341, d337333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336341, d337333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d336342 q = 1) (hb : d337334 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d336342, d337334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d336342, d337334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d336343 q = 1) (hb : d337335 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d336343, d337335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336343, d337335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d336347 q = 1) (hb : d337339 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336347, d337339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336347, d337339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92000 q ha hb
  have h12 (q : Pattern) (ha : d336349 q = 1) (hb : d337341 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336349, d337341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336349, d337341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92001 q ha hb
  have h13 (q : Pattern) (ha : d336350 q = 1) (hb : d337342 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336350, d337342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d336350, d337342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d336351 q = 1) (hb : d337343 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d336351, d337343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d336351, d337343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d336352 q = 1) (hb : d337344 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d336352, d337344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d336352, d337344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d336353 q = 1) (hb : d337345 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d336353, d337345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336353, d337345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d336437 q = 1) (hb : d337431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336437, d337431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336437, d337431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92014 q ha hb
  have h18 (q : Pattern) (ha : d336444 q = 1) (hb : d337442 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336444, d337442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336444, d337442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92016 q ha hb
  have h19 (q : Pattern) (ha : d336445 q = 1) (hb : d337443 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336445, d337443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d336445, d337443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d336446 q = 1) (hb : d337444 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d336446, d337444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d336446, d337444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d336447 q = 1) (hb : d337445 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d336447, d337445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d336447, d337445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d336448 q = 1) (hb : d337446 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d336448, d337446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d336448, d337446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d336449 q = 1) (hb : d337447 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d336449, d337447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d336449, d337447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro92018 (p : Pattern) (ha : d336455 p = 1) (hb : d337453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336450 q = 1) (hb : d337448 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d336450, d337448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336450, d337448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92017 q ha hb
  have h2 (q : Pattern) (ha : d336451 q = 1) (hb : d337449 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d336451, d337449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336451, d337449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336452 q = 1) (hb : d337450 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d336452, d337450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336452, d337450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336453 q = 1) (hb : d337451 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d336453, d337451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336453, d337451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336454 q = 1) (hb : d337452 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d336454, d337452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336454, d337452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336455 q = 1) (hb : d337453 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d336455, d337453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336455, d337453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92019 (p : Pattern) (ha : d39244 p = 1) (hb : d52989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52973 q = 1) : d0 q = 1 := by
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
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d52107 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1519 q = 1) (hb : d52960 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1531 q = 1) (hb : d52972 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1531, d52972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1531, d52972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1547 q = 1) (hb : d52988 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1547, d52988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1547, d52988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d39244 q = 1) (hb : d52989 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d39244, d52989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39244, d52989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro92020 (p : Pattern) (ha : d336462 p = 1) (hb : d337462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52989 q = 1) (hb : d337457 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d337457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d337457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92019 q hb ha
  have h3 (q : Pattern) (ha : d336459 q = 1) (hb : d337458 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d336459, d337458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336459, d337458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336460 q = 1) (hb : d337459 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d336460, d337459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336460, d337459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d336460 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d336460 q = 1) (hb : d337460 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d337460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d336461 q = 1) (hb : d337461 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d336461, d337461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336461, d337461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336462 q = 1) (hb : d337462 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d336462, d337462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336462, d337462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92021 (p : Pattern) (ha : d336469 p = 1) (hb : d337467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d336000 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52989 q = 1) (hb : d337457 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d337457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d337457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92019 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d336459 q = 1) (hb : d337458 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d336459, d337458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336459, d337458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d336467 q = 1) (hb : d337459 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d336467, d337459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336467, d337459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d336467 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d336467 q = 1) (hb : d337460 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d337460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d336468 q = 1) (hb : d337461 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d336468, d337461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336468, d337461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h9 (q : Pattern) (ha : d336469 q = 1) (hb : d337467 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d336469, d337467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d336469, d337467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h9 p ha hb
theorem andIntro92022 (p : Pattern) (ha : d336480 p = 1) (hb : d337476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52989 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52989 q = 1) (hb : d337457 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d337457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92019 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d336459 q = 1) (hb : d337458 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d336459, d337458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336459, d337458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d336475 q = 1) (hb : d337473 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d336475, d337473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336475, d337473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d336475 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d336475 q = 1) (hb : d337474 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d337474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d336476 q = 1) (hb : d337475 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d336476, d337475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336476, d337475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53000 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1575 q = 1) (hb : d53000 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51870 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1115 q = 1) (hb : d51870 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h12 (q : Pattern) (ha : d1576 q = 1) (hb : d336477 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, d336477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1576, d336477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1593 q = 1) (hb : d336478 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1593, d336478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1593, d336478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d336478 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1594 q = 1) (hb : d336478 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1595 q = 1) (hb : d336479 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1595, d336479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1595, d336479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d336480 q = 1) (hb : d337476 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d336480, d337476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336480, d337476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro92023 (p : Pattern) (ha : d336486 p = 1) (hb : d337482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336463 q = 1) (hb : d337463 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336463, d337463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92020 q ha hb
    | true =>
      simp only [d336463, d337463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336464 q = 1) (hb : d337464 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336464, d337464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336464, d337464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336465 q = 1) (hb : d337465 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336465, d337465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336465, d337465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336466 q = 1) (hb : d337466 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336466, d337466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336466, d337466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336470 q = 1) (hb : d337468 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336470, d337468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92021 q ha hb
    | true =>
      simp only [d336470, d337468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336471 q = 1) (hb : d337469 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336471, d337469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336471, d337469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336472 q = 1) (hb : d337470 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336472, d337470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336472, d337470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336473 q = 1) (hb : d337471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336473, d337471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336473, d337471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d336474 q = 1) (hb : d337472 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336474, d337472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336474, d337472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336481 q = 1) (hb : d337477 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336481, d337477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92022 q ha hb
    | true =>
      simp only [d336481, d337477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d336482 q = 1) (hb : d337478 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336482, d337478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336482, d337478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d336483 q = 1) (hb : d337479 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336483, d337479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336483, d337479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d336484 q = 1) (hb : d337480 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336484, d337480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d336484, d337480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d336485 q = 1) (hb : d337481 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336485, d337481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336485, d337481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d336486 q = 1) (hb : d337482 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336486, d337482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d336486, d337482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro92024 (p : Pattern) (ha : d336490 p = 1) (hb : d337486 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d336000 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52989 q = 1) (hb : d337457 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d337457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d337457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92019 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d336459 q = 1) (hb : d337458 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d336459, d337458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336459, d337458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d336467 q = 1) (hb : d337459 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d336467, d337459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336467, d337459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d336467 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d336467 q = 1) (hb : d337460 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d337460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d336468 q = 1) (hb : d337461 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d336468, d337461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336468, d337461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53004 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5128 q = 1) (hb : d53004 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
  have h11 (q : Pattern) (ha : d5129 q = 1) (hb : d336487 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, d336487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5129, d336487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d336488 q = 1) (hb : d337483 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d336488, d337483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336488, d337483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d336488 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d336488 q = 1) (hb : d337484 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d337484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d337484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d336489 q = 1) (hb : d337485 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d336489, d337485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d336489, d337485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h16 (q : Pattern) (ha : d336490 q = 1) (hb : d337486 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d336490, d337486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d336490, d337486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro92025 (p : Pattern) (ha : d336495 p = 1) (hb : d337491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52989 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52989 q = 1) (hb : d337457 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d337457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92019 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d336459 q = 1) (hb : d337458 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d336459, d337458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336459, d337458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53004 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5128 q = 1) (hb : d53004 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
  have h6 (q : Pattern) (ha : d5129 q = 1) (hb : d336487 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, d336487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5129, d336487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d336488 q = 1) (hb : d337483 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d336488, d337483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336488, d337483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d336488 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d336488 q = 1) (hb : d337484 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d337484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d337484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d336489 q = 1) (hb : d337485 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d336489, d337485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d336489, d337485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53000 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d1575 q = 1) (hb : d53000 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d51870 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1115 q = 1) (hb : d51870 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h15 (q : Pattern) (ha : d1576 q = 1) (hb : d336477 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, d336477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1576, d336477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1593 q = 1) (hb : d336478 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1593, d336478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1593, d336478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d336478 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d1594 q = 1) (hb : d336478 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1595 q = 1) (hb : d336479 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1595, d336479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d1595, d336479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h20 (q : Pattern) (ha : d336495 q = 1) (hb : d337491 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d336495, d337491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336495, d337491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  exact h20 p ha hb
theorem andIntro92026 (p : Pattern) (ha : d336502 p = 1) (hb : d337498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336491 q = 1) (hb : d337487 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336491, d337487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92024 q ha hb
    | true =>
      simp only [d336491, d337487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336492 q = 1) (hb : d337488 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336492, d337488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336492, d337488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336493 q = 1) (hb : d337489 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336493, d337489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336493, d337489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336494 q = 1) (hb : d337490 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336494, d337490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336494, d337490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336496 q = 1) (hb : d337492 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336496, d337492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92025 q ha hb
    | true =>
      simp only [d336496, d337492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336497 q = 1) (hb : d337493 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336497, d337493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336497, d337493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336498 q = 1) (hb : d337494 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336498, d337494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336498, d337494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336499 q = 1) (hb : d337495 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336499, d337495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336499, d337495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d336500 q = 1) (hb : d337496 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336500, d337496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336500, d337496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336481 q = 1) (hb : d337477 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336481, d337477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92022 q ha hb
    | true =>
      simp only [d336481, d337477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d336482 q = 1) (hb : d337478 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336482, d337478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336482, d337478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d336483 q = 1) (hb : d337479 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336483, d337479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336483, d337479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d336484 q = 1) (hb : d337480 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336484, d337480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d336484, d337480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d336501 q = 1) (hb : d337497 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336501, d337497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d336501, d337497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d336502 q = 1) (hb : d337498 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336502, d337498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d336502, d337498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro92027 (p : Pattern) (ha : d1596 p = 1) (hb : d336507 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53000 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1575 q = 1) (hb : d53000 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51870 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1115 q = 1) (hb : d51870 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h4 (q : Pattern) (ha : d1576 q = 1) (hb : d336477 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, d336477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1576, d336477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1593 q = 1) (hb : d336478 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1593, d336478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1593, d336478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d336478 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1594 q = 1) (hb : d336478 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1595 q = 1) (hb : d336479 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1595, d336479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1595, d336479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h10 (q : Pattern) (ha : d1596 q = 1) (hb : d336507 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1596, d336507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1596, d336507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h10 p ha hb
theorem andIntro92028 (p : Pattern) (ha : d336513 p = 1) (hb : d337503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336496 q = 1) (hb : d337492 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336496, d337492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92025 q ha hb
    | true =>
      simp only [d336496, d337492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336497 q = 1) (hb : d337493 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336497, d337493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336497, d337493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336498 q = 1) (hb : d337494 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336498, d337494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336498, d337494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336499 q = 1) (hb : d337495 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336499, d337495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336499, d337495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336506 q = 1) (hb : d337502 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336506, d337502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336506, d337502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d1597 q = 1) (hb : d336508 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1597, d336508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92027 q ha hb
    | true =>
      simp only [d1597, d336508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1598 q = 1) (hb : d336509 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1598, d336509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1598, d336509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1599 q = 1) (hb : d336510 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1599, d336510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1599, d336510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1600 q = 1) (hb : d336511 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1600, d336511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1600, d336511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1601 q = 1) (hb : d336512 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1601, d336512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1601, d336512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d336513 q = 1) (hb : d337503 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336513, d337503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336513, d337503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro92029 (p : Pattern) (ha : d336520 p = 1) (hb : d337510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336503 q = 1) (hb : d337499 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336503, d337499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92023 q ha hb
    | true =>
      simp only [d336503, d337499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92026 q ha hb
  have h2 (q : Pattern) (ha : d336504 q = 1) (hb : d337500 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336504, d337500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336504, d337500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336505 q = 1) (hb : d337501 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336505, d337501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336505, d337501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336514 q = 1) (hb : d337504 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336514, d337504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92026 q ha hb
    | true =>
      simp only [d336514, d337504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92028 q ha hb
  have h5 (q : Pattern) (ha : d336515 q = 1) (hb : d337505 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336515, d337505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336515, d337505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336516 q = 1) (hb : d337506 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336516, d337506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336516, d337506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336517 q = 1) (hb : d337507 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336517, d337507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336517, d337507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336518 q = 1) (hb : d337508 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336518, d337508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336518, d337508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d336519 q = 1) (hb : d337509 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d336519, d337509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336519, d337509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336520 q = 1) (hb : d337510 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d336520, d337510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d336520, d337510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro92030 (p : Pattern) (ha : d336524 p = 1) (hb : d337514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336514 q = 1) (hb : d337504 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336514, d337504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92026 q ha hb
    | true =>
      simp only [d336514, d337504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92028 q ha hb
  have h2 (q : Pattern) (ha : d336515 q = 1) (hb : d337505 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336515, d337505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336515, d337505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336516 q = 1) (hb : d337506 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336516, d337506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336516, d337506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336518 q = 1) (hb : d337508 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336518, d337508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336518, d337508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336523 q = 1) (hb : d337513 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d336523, d337513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336523, d337513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336524 q = 1) (hb : d337514 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d336524, d337514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336524, d337514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92031 (p : Pattern) (ha : d336530 p = 1) (hb : d337520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336521 q = 1) (hb : d337511 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336521, d337511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92029 q ha hb
    | true =>
      simp only [d336521, d337511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336522 q = 1) (hb : d337512 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336522, d337512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336522, d337512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336525 q = 1) (hb : d337515 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92030 q ha hb
    | true =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336526 q = 1) (hb : d337516 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336527 q = 1) (hb : d337517 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336527, d337517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336527, d337517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336528 q = 1) (hb : d337518 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336528, d337518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336528, d337518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336529 q = 1) (hb : d337519 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336529, d337519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336529, d337519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336530 q = 1) (hb : d337520 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336530, d337520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336530, d337520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92032 (p : Pattern) (ha : d336534 p = 1) (hb : d337524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336525 q = 1) (hb : d337515 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92030 q ha hb
    | true =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336526 q = 1) (hb : d337516 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336531 q = 1) (hb : d337521 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336531, d337521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336531, d337521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336532 q = 1) (hb : d337522 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336532, d337522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336532, d337522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336533 q = 1) (hb : d337523 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336533, d337523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336533, d337523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336534 q = 1) (hb : d337524 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336534, d337524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336534, d337524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92033 (p : Pattern) (ha : d336540 p = 1) (hb : d337530 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336535 q = 1) (hb : d337525 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336535, d337525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92031 q ha hb
    | true =>
      simp only [d336535, d337525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92032 q ha hb
  have h2 (q : Pattern) (ha : d336536 q = 1) (hb : d337526 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336536, d337526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336536, d337526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336537 q = 1) (hb : d337527 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336537, d337527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336537, d337527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336538 q = 1) (hb : d337528 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336538, d337528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336538, d337528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336539 q = 1) (hb : d337529 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336539, d337529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336539, d337529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336540 q = 1) (hb : d337530 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336540, d337530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336540, d337530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92034 (p : Pattern) (ha : d336543 p = 1) (hb : d337533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336521 q = 1) (hb : d337511 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336521, d337511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92029 q ha hb
    | true =>
      simp only [d336521, d337511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336522 q = 1) (hb : d337512 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336522, d337512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336522, d337512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336525 q = 1) (hb : d337515 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92030 q ha hb
    | true =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336526 q = 1) (hb : d337516 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336527 q = 1) (hb : d337517 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336527, d337517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336527, d337517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336528 q = 1) (hb : d337518 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336528, d337518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336528, d337518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336529 q = 1) (hb : d337519 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336529, d337519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336529, d337519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336543 q = 1) (hb : d337533 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336543, d337533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336543, d337533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro92035 (p : Pattern) (ha : d336544 p = 1) (hb : d337534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336525 q = 1) (hb : d337515 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92030 q ha hb
    | true =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336526 q = 1) (hb : d337516 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336531 q = 1) (hb : d337521 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336531, d337521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336531, d337521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336532 q = 1) (hb : d337522 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336532, d337522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336532, d337522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336533 q = 1) (hb : d337523 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336533, d337523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336533, d337523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336544 q = 1) (hb : d337534 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336544, d337534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336544, d337534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92036 (p : Pattern) (ha : d336550 p = 1) (hb : d337540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336535 q = 1) (hb : d337525 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336535, d337525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92031 q ha hb
    | true =>
      simp only [d336535, d337525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92032 q ha hb
  have h2 (q : Pattern) (ha : d336536 q = 1) (hb : d337526 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336536, d337526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336536, d337526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336537 q = 1) (hb : d337527 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336537, d337527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336537, d337527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336538 q = 1) (hb : d337528 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336538, d337528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336538, d337528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336539 q = 1) (hb : d337529 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336539, d337529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336539, d337529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336545 q = 1) (hb : d337535 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336545, d337535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92034 q ha hb
    | true =>
      simp only [d336545, d337535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92035 q ha hb
  have h7 (q : Pattern) (ha : d336546 q = 1) (hb : d337536 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336546, d337536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336546, d337536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336547 q = 1) (hb : d337537 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336547, d337537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336547, d337537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d336548 q = 1) (hb : d337538 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336548, d337538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336548, d337538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336549 q = 1) (hb : d337539 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336549, d337539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336549, d337539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d336550 q = 1) (hb : d337540 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336550, d337540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336550, d337540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro92037 (p : Pattern) (ha : d336555 p = 1) (hb : d337545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336521 q = 1) (hb : d337511 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336521, d337511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92029 q ha hb
    | true =>
      simp only [d336521, d337511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336522 q = 1) (hb : d337512 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336522, d337512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336522, d337512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336525 q = 1) (hb : d337515 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92030 q ha hb
    | true =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336526 q = 1) (hb : d337516 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336527 q = 1) (hb : d337517 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336527, d337517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336527, d337517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336528 q = 1) (hb : d337518 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336528, d337518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336528, d337518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336554 q = 1) (hb : d337544 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336554, d337544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336554, d337544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336555 q = 1) (hb : d337545 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336555, d337545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336555, d337545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92038 (p : Pattern) (ha : d336557 p = 1) (hb : d337547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336525 q = 1) (hb : d337515 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92030 q ha hb
    | true =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336526 q = 1) (hb : d337516 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336531 q = 1) (hb : d337521 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336531, d337521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336531, d337521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336532 q = 1) (hb : d337522 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336532, d337522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336532, d337522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336556 q = 1) (hb : d337546 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336556, d337546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336556, d337546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336557 q = 1) (hb : d337547 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336557, d337547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336557, d337547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92039 (p : Pattern) (ha : d336564 p = 1) (hb : d337554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336521 q = 1) (hb : d337511 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336521, d337511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92029 q ha hb
    | true =>
      simp only [d336521, d337511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336522 q = 1) (hb : d337512 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336522, d337512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336522, d337512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336525 q = 1) (hb : d337515 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92030 q ha hb
    | true =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336526 q = 1) (hb : d337516 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336527 q = 1) (hb : d337517 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336527, d337517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336527, d337517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336562 q = 1) (hb : d337552 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336562, d337552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336562, d337552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336563 q = 1) (hb : d337553 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336563, d337553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336563, d337553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336564 q = 1) (hb : d337554 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336564, d337554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336564, d337554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92040 (p : Pattern) (ha : d336567 p = 1) (hb : d337557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336525 q = 1) (hb : d337515 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92030 q ha hb
    | true =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336526 q = 1) (hb : d337516 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336531 q = 1) (hb : d337521 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336531, d337521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336531, d337521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336565 q = 1) (hb : d337555 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336565, d337555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336565, d337555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336566 q = 1) (hb : d337556 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336566, d337556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336566, d337556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336567 q = 1) (hb : d337557 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336567, d337557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336567, d337557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92041 (p : Pattern) (ha : d336574 p = 1) (hb : d337564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336481 q = 1) (hb : d337477 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336481, d337477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92022 q ha hb
    | true =>
      simp only [d336481, d337477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336482 q = 1) (hb : d337478 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336482, d337478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336482, d337478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336483 q = 1) (hb : d337479 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336483, d337479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336483, d337479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336484 q = 1) (hb : d337480 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336484, d337480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336484, d337480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336485 q = 1) (hb : d337481 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336485, d337481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336485, d337481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336501 q = 1) (hb : d337497 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336501, d337497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336501, d337497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336574 q = 1) (hb : d337564 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336574, d337564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336574, d337564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro92042 (p : Pattern) (ha : d336580 p = 1) (hb : d337570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336571 q = 1) (hb : d337561 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336571, d337561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336571, d337561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92023 q ha hb
  have h2 (q : Pattern) (ha : d336572 q = 1) (hb : d337562 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336572, d337562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336572, d337562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336573 q = 1) (hb : d337563 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336573, d337563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336573, d337563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336575 q = 1) (hb : d337565 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336575, d337565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92023 q ha hb
    | true =>
      simp only [d336575, d337565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92041 q ha hb
  have h5 (q : Pattern) (ha : d336576 q = 1) (hb : d337566 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336576, d337566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336576, d337566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336577 q = 1) (hb : d337567 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336577, d337567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336577, d337567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336578 q = 1) (hb : d337568 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336578, d337568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336578, d337568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336503 q = 1) (hb : d337499 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336503, d337499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92023 q ha hb
    | true =>
      simp only [d336503, d337499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92026 q ha hb
  have h9 (q : Pattern) (ha : d336504 q = 1) (hb : d337500 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336504, d337500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336504, d337500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336505 q = 1) (hb : d337501 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336505, d337501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336505, d337501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d336514 q = 1) (hb : d337504 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336514, d337504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92026 q ha hb
    | true =>
      simp only [d336514, d337504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92028 q ha hb
  have h12 (q : Pattern) (ha : d336515 q = 1) (hb : d337505 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336515, d337505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336515, d337505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d336516 q = 1) (hb : d337506 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336516, d337506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336516, d337506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d336517 q = 1) (hb : d337507 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336517, d337507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336517, d337507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d336579 q = 1) (hb : d337569 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d336579, d337569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336579, d337569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d336580 q = 1) (hb : d337570 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d336580, d337570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d336580, d337570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro92043 (p : Pattern) (ha : d336586 p = 1) (hb : d337576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336581 q = 1) (hb : d337571 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336581, d337571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92042 q ha hb
    | true =>
      simp only [d336581, d337571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336582 q = 1) (hb : d337572 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336582, d337572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336582, d337572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336521 q = 1) (hb : d337511 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336521, d337511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92029 q ha hb
    | true =>
      simp only [d336521, d337511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336522 q = 1) (hb : d337512 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336522, d337512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336522, d337512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336583 q = 1) (hb : d337573 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336583, d337573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336583, d337573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336584 q = 1) (hb : d337574 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336584, d337574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336584, d337574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336585 q = 1) (hb : d337575 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336585, d337575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336585, d337575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336586 q = 1) (hb : d337576 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336586, d337576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336586, d337576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92044 (p : Pattern) (ha : d336591 p = 1) (hb : d337579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52989 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52989 q = 1) (hb : d337457 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d337457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92019 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d336459 q = 1) (hb : d337458 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d336459, d337458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336459, d337458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d336475 q = 1) (hb : d337473 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d336475, d337473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336475, d337473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d336475 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d336475 q = 1) (hb : d337474 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d337474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d336476 q = 1) (hb : d337475 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d336476, d337475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336476, d337475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53004 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d5128 q = 1) (hb : d53004 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
  have h10 (q : Pattern) (ha : d5129 q = 1) (hb : d336487 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, d336487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5129, d336487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d26754 q = 1) (hb : d336589 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26754, d336589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26754, d336589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d336589 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d239545 q = 1) (hb : d336589 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d239545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d239545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d239546 q = 1) (hb : d336590 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d239546, d336590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d239546, d336590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h15 (q : Pattern) (ha : d336591 q = 1) (hb : d337579 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d336591, d337579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336591, d337579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro92045 (p : Pattern) (ha : d336597 p = 1) (hb : d337585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336491 q = 1) (hb : d337487 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336491, d337487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92024 q ha hb
    | true =>
      simp only [d336491, d337487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336492 q = 1) (hb : d337488 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336492, d337488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336492, d337488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336493 q = 1) (hb : d337489 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336493, d337489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336493, d337489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336494 q = 1) (hb : d337490 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336494, d337490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336494, d337490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336496 q = 1) (hb : d337492 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336496, d337492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92025 q ha hb
    | true =>
      simp only [d336496, d337492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336497 q = 1) (hb : d337493 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336497, d337493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336497, d337493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336498 q = 1) (hb : d337494 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336498, d337494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336498, d337494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336499 q = 1) (hb : d337495 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336499, d337495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336499, d337495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d336500 q = 1) (hb : d337496 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336500, d337496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336500, d337496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336592 q = 1) (hb : d337580 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336592, d337580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92044 q ha hb
    | true =>
      simp only [d336592, d337580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d336593 q = 1) (hb : d337581 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336593, d337581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336593, d337581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d336594 q = 1) (hb : d337582 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336594, d337582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336594, d337582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d336595 q = 1) (hb : d337583 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336595, d337583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d336595, d337583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d336596 q = 1) (hb : d337584 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336596, d337584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d336596, d337584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d336597 q = 1) (hb : d337585 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336597, d337585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d336597, d337585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro92046 (p : Pattern) (ha : d336598 p = 1) (hb : d337586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52989 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52989 q = 1) (hb : d337457 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d337457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92019 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d336459 q = 1) (hb : d337458 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d336459, d337458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336459, d337458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53004 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5128 q = 1) (hb : d53004 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
  have h6 (q : Pattern) (ha : d5129 q = 1) (hb : d336487 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, d336487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5129, d336487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d336488 q = 1) (hb : d337483 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d336488, d337483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336488, d337483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d336488 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d336488 q = 1) (hb : d337484 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d337484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d337484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d336489 q = 1) (hb : d337485 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d336489, d337485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d336489, d337485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h11 (q : Pattern) (ha : d26754 q = 1) (hb : d336589 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26754, d336589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26754, d336589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d336589 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d239545 q = 1) (hb : d336589 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d239545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d239545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d239546 q = 1) (hb : d336590 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d239546, d336590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d239546, d336590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h15 (q : Pattern) (ha : d336598 q = 1) (hb : d337586 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d336598, d337586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336598, d337586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro92047 (p : Pattern) (ha : d336604 p = 1) (hb : d337592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336599 q = 1) (hb : d337587 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336599, d337587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92046 q ha hb
    | true =>
      simp only [d336599, d337587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336600 q = 1) (hb : d337588 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336600, d337588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336600, d337588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336601 q = 1) (hb : d337589 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336601, d337589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336601, d337589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336602 q = 1) (hb : d337590 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336602, d337590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336602, d337590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336603 q = 1) (hb : d337591 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336603, d337591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336603, d337591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336604 q = 1) (hb : d337592 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336604, d337592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336604, d337592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92048 (p : Pattern) (ha : d336610 p = 1) (hb : d337598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336503 q = 1) (hb : d337499 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336503, d337499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92023 q ha hb
    | true =>
      simp only [d336503, d337499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92026 q ha hb
  have h2 (q : Pattern) (ha : d336504 q = 1) (hb : d337500 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336504, d337500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336504, d337500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336505 q = 1) (hb : d337501 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336505, d337501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336505, d337501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336514 q = 1) (hb : d337504 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336514, d337504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92026 q ha hb
    | true =>
      simp only [d336514, d337504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92028 q ha hb
  have h5 (q : Pattern) (ha : d336515 q = 1) (hb : d337505 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336515, d337505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336515, d337505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336516 q = 1) (hb : d337506 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336516, d337506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336516, d337506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336517 q = 1) (hb : d337507 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336517, d337507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336517, d337507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336605 q = 1) (hb : d337593 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336605, d337593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92045 q ha hb
    | true =>
      simp only [d336605, d337593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92047 q ha hb
  have h9 (q : Pattern) (ha : d336606 q = 1) (hb : d337594 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336606, d337594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336606, d337594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336607 q = 1) (hb : d337595 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336607, d337595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336607, d337595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d336608 q = 1) (hb : d337596 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336608, d337596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336608, d337596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d336609 q = 1) (hb : d337597 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d336609, d337597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336609, d337597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d336610 q = 1) (hb : d337598 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d336610, d337598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d336610, d337598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro92049 (p : Pattern) (ha : d336616 p = 1) (hb : d337604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336611 q = 1) (hb : d337599 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336611, d337599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92048 q ha hb
    | true =>
      simp only [d336611, d337599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336612 q = 1) (hb : d337600 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336612, d337600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336612, d337600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336613 q = 1) (hb : d337601 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336613, d337601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336613, d337601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336614 q = 1) (hb : d337602 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336614, d337602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336614, d337602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336615 q = 1) (hb : d337603 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336615, d337603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336615, d337603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336616 q = 1) (hb : d337604 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336616, d337604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336616, d337604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92050 (p : Pattern) (ha : d336622 p = 1) (hb : d337610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336558 q = 1) (hb : d337548 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336558, d337548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92037 q ha hb
    | true =>
      simp only [d336558, d337548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92038 q ha hb
  have h2 (q : Pattern) (ha : d336559 q = 1) (hb : d337549 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336559, d337549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336559, d337549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336560 q = 1) (hb : d337550 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336560, d337550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336560, d337550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336561 q = 1) (hb : d337551 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336561, d337551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336561, d337551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336568 q = 1) (hb : d337558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336568, d337558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92039 q ha hb
    | true =>
      simp only [d336568, d337558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92040 q ha hb
  have h6 (q : Pattern) (ha : d336569 q = 1) (hb : d337559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336569, d337559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336569, d337559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336570 q = 1) (hb : d337560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336570, d337560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336570, d337560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336587 q = 1) (hb : d337577 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336587, d337577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92043 q ha hb
    | true =>
      simp only [d336587, d337577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92031 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d336535 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d336588 q = 1) (hb : d337578 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336588, d337578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d336588, d337578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d336617 q = 1) (hb : d337605 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336617, d337605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92049 q ha hb
    | true =>
      simp only [d336617, d337605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d336618 q = 1) (hb : d337606 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336618, d337606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d336618, d337606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d336619 q = 1) (hb : d337607 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336619, d337607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336619, d337607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d336620 q = 1) (hb : d337608 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336620, d337608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336620, d337608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d336621 q = 1) (hb : d337609 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336621, d337609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336621, d337609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d336622 q = 1) (hb : d337610 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336622, d337610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336622, d337610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro92051 (p : Pattern) (ha : d336623 p = 1) (hb : d337611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336521 q = 1) (hb : d337511 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336521, d337511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92029 q ha hb
    | true =>
      simp only [d336521, d337511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336522 q = 1) (hb : d337512 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336522, d337512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336522, d337512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336525 q = 1) (hb : d337515 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92030 q ha hb
    | true =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336526 q = 1) (hb : d337516 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336527 q = 1) (hb : d337517 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336527, d337517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336527, d337517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336528 q = 1) (hb : d337518 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336528, d337518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336528, d337518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336554 q = 1) (hb : d337544 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336554, d337544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336554, d337544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336623 q = 1) (hb : d337611 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336623, d337611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336623, d337611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro92052 (p : Pattern) (ha : d336624 p = 1) (hb : d337612 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336525 q = 1) (hb : d337515 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92030 q ha hb
    | true =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336526 q = 1) (hb : d337516 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336531 q = 1) (hb : d337521 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336531, d337521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336531, d337521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336532 q = 1) (hb : d337522 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336532, d337522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336532, d337522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336556 q = 1) (hb : d337546 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336556, d337546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336556, d337546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336624 q = 1) (hb : d337612 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336624, d337612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336624, d337612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92053 (p : Pattern) (ha : d336629 p = 1) (hb : d337617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336521 q = 1) (hb : d337511 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336521, d337511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92029 q ha hb
    | true =>
      simp only [d336521, d337511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336522 q = 1) (hb : d337512 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336522, d337512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336522, d337512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336525 q = 1) (hb : d337515 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92030 q ha hb
    | true =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336526 q = 1) (hb : d337516 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336527 q = 1) (hb : d337517 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336527, d337517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336527, d337517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336562 q = 1) (hb : d337552 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336562, d337552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336562, d337552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336563 q = 1) (hb : d337553 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336563, d337553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336563, d337553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336629 q = 1) (hb : d337617 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336629, d337617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336629, d337617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro92054 (p : Pattern) (ha : d336630 p = 1) (hb : d337618 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336525 q = 1) (hb : d337515 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92030 q ha hb
    | true =>
      simp only [d336525, d337515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336526 q = 1) (hb : d337516 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336526, d337516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336531 q = 1) (hb : d337521 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336531, d337521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336531, d337521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336565 q = 1) (hb : d337555 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336565, d337555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336565, d337555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336566 q = 1) (hb : d337556 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336566, d337556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336566, d337556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336630 q = 1) (hb : d337618 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336630, d337618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336630, d337618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92055 (p : Pattern) (ha : d336634 p = 1) (hb : d337622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336581 q = 1) (hb : d337571 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336581, d337571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92042 q ha hb
    | true =>
      simp only [d336581, d337571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336582 q = 1) (hb : d337572 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336582, d337572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336582, d337572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336521 q = 1) (hb : d337511 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336521, d337511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92029 q ha hb
    | true =>
      simp only [d336521, d337511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336522 q = 1) (hb : d337512 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336522, d337512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336522, d337512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336583 q = 1) (hb : d337573 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336583, d337573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336583, d337573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336584 q = 1) (hb : d337574 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336584, d337574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336584, d337574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336585 q = 1) (hb : d337575 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336585, d337575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336585, d337575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336634 q = 1) (hb : d337622 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336634, d337622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336634, d337622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro92056 (p : Pattern) (ha : d336637 p = 1) (hb : d337625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336611 q = 1) (hb : d337599 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336611, d337599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92048 q ha hb
    | true =>
      simp only [d336611, d337599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336612 q = 1) (hb : d337600 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336612, d337600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336612, d337600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336613 q = 1) (hb : d337601 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336613, d337601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336613, d337601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336614 q = 1) (hb : d337602 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336614, d337602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336614, d337602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336615 q = 1) (hb : d337603 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336615, d337603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336615, d337603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336637 q = 1) (hb : d337625 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336637, d337625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336637, d337625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92057 (p : Pattern) (ha : d336643 p = 1) (hb : d337631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336558 q = 1) (hb : d337548 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336558, d337548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92037 q ha hb
    | true =>
      simp only [d336558, d337548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92038 q ha hb
  have h2 (q : Pattern) (ha : d336559 q = 1) (hb : d337549 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336559, d337549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336559, d337549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336560 q = 1) (hb : d337550 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336560, d337550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336560, d337550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336561 q = 1) (hb : d337551 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336561, d337551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336561, d337551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336568 q = 1) (hb : d337558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336568, d337558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92039 q ha hb
    | true =>
      simp only [d336568, d337558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92040 q ha hb
  have h6 (q : Pattern) (ha : d336569 q = 1) (hb : d337559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336569, d337559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336569, d337559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336570 q = 1) (hb : d337560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336570, d337560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336570, d337560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336587 q = 1) (hb : d337577 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336587, d337577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92043 q ha hb
    | true =>
      simp only [d336587, d337577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92031 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d336535 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d336588 q = 1) (hb : d337578 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336588, d337578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d336588, d337578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d336617 q = 1) (hb : d337605 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336617, d337605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92049 q ha hb
    | true =>
      simp only [d336617, d337605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d336618 q = 1) (hb : d337606 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336618, d337606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d336618, d337606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d336619 q = 1) (hb : d337607 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336619, d337607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336619, d337607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d336620 q = 1) (hb : d337608 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336620, d337608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336620, d337608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d336621 q = 1) (hb : d337609 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336621, d337609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336621, d337609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d336625 q = 1) (hb : d337613 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336625, d337613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92051 q ha hb
    | true =>
      simp only [d336625, d337613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92052 q ha hb
  have h17 (q : Pattern) (ha : d336626 q = 1) (hb : d337614 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336626, d337614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336626, d337614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d336627 q = 1) (hb : d337615 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336627, d337615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d336627, d337615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d336628 q = 1) (hb : d337616 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336628, d337616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336628, d337616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d336631 q = 1) (hb : d337619 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336631, d337619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92053 q ha hb
    | true =>
      simp only [d336631, d337619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92054 q ha hb
  have h21 (q : Pattern) (ha : d336632 q = 1) (hb : d337620 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336632, d337620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336632, d337620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d336633 q = 1) (hb : d337621 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336633, d337621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d336633, d337621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d336635 q = 1) (hb : d337623 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336635, d337623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92055 q ha hb
    | true =>
      simp only [d336635, d337623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92034 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d336545 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d336636 q = 1) (hb : d337624 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336636, d337624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d336636, d337624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d336638 q = 1) (hb : d337626 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336638, d337626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92056 q ha hb
    | true =>
      simp only [d336638, d337626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d336639 q = 1) (hb : d337627 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336639, d337627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d336639, d337627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d336640 q = 1) (hb : d337628 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336640, d337628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d336640, d337628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d336641 q = 1) (hb : d337629 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336641, d337629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d336641, d337629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d336642 q = 1) (hb : d337630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336642, d337630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d336642, d337630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d336643 q = 1) (hb : d337631 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336643, d337631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d336643, d337631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro92058 (p : Pattern) (ha : d336650 p = 1) (hb : d337638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336535 q = 1) (hb : d337525 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336535, d337525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92031 q ha hb
    | true =>
      simp only [d336535, d337525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92032 q ha hb
  have h2 (q : Pattern) (ha : d336536 q = 1) (hb : d337526 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336536, d337526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336536, d337526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336537 q = 1) (hb : d337527 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336537, d337527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336537, d337527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336538 q = 1) (hb : d337528 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336538, d337528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336538, d337528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336539 q = 1) (hb : d337529 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336539, d337529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336539, d337529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336645 q = 1) (hb : d337633 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336645, d337633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92032 q ha hb
    | true =>
      simp only [d336645, d337633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336646 q = 1) (hb : d337634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336646, d337634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336646, d337634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336647 q = 1) (hb : d337635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336647, d337635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336647, d337635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d336648 q = 1) (hb : d337636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336648, d337636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336648, d337636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336649 q = 1) (hb : d337637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336649, d337637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336649, d337637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d336650 q = 1) (hb : d337638 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336650, d337638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336650, d337638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro92059 (p : Pattern) (ha : d336656 p = 1) (hb : d337644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336645 q = 1) (hb : d337633 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336645, d337633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92032 q ha hb
    | true =>
      simp only [d336645, d337633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336646 q = 1) (hb : d337634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336646, d337634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336646, d337634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336647 q = 1) (hb : d337635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336647, d337635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336647, d337635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336648 q = 1) (hb : d337636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336648, d337636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336648, d337636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336649 q = 1) (hb : d337637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336649, d337637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336649, d337637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336651 q = 1) (hb : d337639 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336651, d337639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92035 q ha hb
    | true =>
      simp only [d336651, d337639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336652 q = 1) (hb : d337640 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336652, d337640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336652, d337640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336653 q = 1) (hb : d337641 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336653, d337641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336653, d337641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d336654 q = 1) (hb : d337642 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336654, d337642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336654, d337642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336655 q = 1) (hb : d337643 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336655, d337643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336655, d337643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d336656 q = 1) (hb : d337644 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336656, d337644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336656, d337644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro92060 (p : Pattern) (ha : d336663 p = 1) (hb : d337651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336635 q = 1) (hb : d337623 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336635, d337623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92055 q ha hb
    | true =>
      simp only [d336635, d337623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92034 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d336545 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d336636 q = 1) (hb : d337624 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336636, d337624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336636, d337624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d336638 q = 1) (hb : d337626 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336638, d337626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92056 q ha hb
    | true =>
      simp only [d336638, d337626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336639 q = 1) (hb : d337627 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336639, d337627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336639, d337627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336640 q = 1) (hb : d337628 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336640, d337628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336640, d337628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336661 q = 1) (hb : d337649 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336661, d337649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336661, d337649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336662 q = 1) (hb : d337650 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336662, d337650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336662, d337650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d336663 q = 1) (hb : d337651 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336663, d337651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336663, d337651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro92061 (p : Pattern) (ha : d336665 p = 1) (hb : d337653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336651 q = 1) (hb : d337639 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336651, d337639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92035 q ha hb
    | true =>
      simp only [d336651, d337639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336652 q = 1) (hb : d337640 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336652, d337640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336652, d337640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336653 q = 1) (hb : d337641 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336653, d337641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336653, d337641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336654 q = 1) (hb : d337642 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336654, d337642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336654, d337642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336655 q = 1) (hb : d337643 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336655, d337643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336655, d337643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336665 q = 1) (hb : d337653 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336665, d337653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336665, d337653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92062 (p : Pattern) (ha : d336685 p = 1) (hb : d337673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336671 q = 1) (hb : d337659 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336671, d337659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336671, d337659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92020 q ha hb
  have h2 (q : Pattern) (ha : d336463 q = 1) (hb : d337463 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336463, d337463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92020 q ha hb
    | true =>
      simp only [d336463, d337463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336672 q = 1) (hb : d337660 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336672, d337660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336672, d337660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336464 q = 1) (hb : d337464 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336464, d337464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336464, d337464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336673 q = 1) (hb : d337661 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336673, d337661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336673, d337661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336674 q = 1) (hb : d337662 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336674, d337662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336674, d337662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336675 q = 1) (hb : d337663 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336675, d337663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336675, d337663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92021 q ha hb
  have h8 (q : Pattern) (ha : d336470 q = 1) (hb : d337468 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336470, d337468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92021 q ha hb
    | true =>
      simp only [d336470, d337468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d336676 q = 1) (hb : d337664 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336676, d337664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336676, d337664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336471 q = 1) (hb : d337469 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336471, d337469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d336471, d337469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d336677 q = 1) (hb : d337665 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336677, d337665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d336677, d337665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d336678 q = 1) (hb : d337666 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336678, d337666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d336678, d337666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d336679 q = 1) (hb : d337667 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336679, d337667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336679, d337667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d336680 q = 1) (hb : d337668 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336680, d337668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336680, d337668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92022 q ha hb
  have h15 (q : Pattern) (ha : d336481 q = 1) (hb : d337477 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336481, d337477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92022 q ha hb
    | true =>
      simp only [d336481, d337477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d336681 q = 1) (hb : d337669 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336681, d337669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d336681, d337669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d336482 q = 1) (hb : d337478 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336482, d337478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d336482, d337478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d336682 q = 1) (hb : d337670 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336682, d337670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d336682, d337670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d336683 q = 1) (hb : d337671 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336683, d337671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d336683, d337671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d336684 q = 1) (hb : d337672 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336684, d337672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336684, d337672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d336685 q = 1) (hb : d337673 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336685, d337673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d336685, d337673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro92063 (p : Pattern) (ha : d336690 p = 1) (hb : d337678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336680 q = 1) (hb : d337668 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336680, d337668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336680, d337668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92022 q ha hb
  have h2 (q : Pattern) (ha : d336481 q = 1) (hb : d337477 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336481, d337477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92022 q ha hb
    | true =>
      simp only [d336481, d337477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336681 q = 1) (hb : d337669 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336681, d337669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336681, d337669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336482 q = 1) (hb : d337478 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336482, d337478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336482, d337478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336682 q = 1) (hb : d337670 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336682, d337670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336682, d337670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336683 q = 1) (hb : d337671 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336683, d337671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336683, d337671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336684 q = 1) (hb : d337672 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336684, d337672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336684, d337672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336689 q = 1) (hb : d337677 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336689, d337677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336689, d337677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d336690 q = 1) (hb : d337678 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336690, d337678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336690, d337678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro92064 (p : Pattern) (ha : d336704 p = 1) (hb : d337692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336695 q = 1) (hb : d337683 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336695, d337683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336695, d337683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92024 q ha hb
  have h2 (q : Pattern) (ha : d336491 q = 1) (hb : d337487 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336491, d337487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92024 q ha hb
    | true =>
      simp only [d336491, d337487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336696 q = 1) (hb : d337684 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336696, d337684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336696, d337684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336492 q = 1) (hb : d337488 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336492, d337488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336492, d337488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336697 q = 1) (hb : d337685 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336697, d337685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336697, d337685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336698 q = 1) (hb : d337686 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336698, d337686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336698, d337686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336699 q = 1) (hb : d337687 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336699, d337687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336699, d337687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92025 q ha hb
  have h8 (q : Pattern) (ha : d336496 q = 1) (hb : d337492 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336496, d337492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92025 q ha hb
    | true =>
      simp only [d336496, d337492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d336700 q = 1) (hb : d337688 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336700, d337688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336700, d337688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336497 q = 1) (hb : d337493 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336497, d337493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d336497, d337493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d336701 q = 1) (hb : d337689 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336701, d337689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d336701, d337689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d336702 q = 1) (hb : d337690 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336702, d337690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d336702, d337690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d336703 q = 1) (hb : d337691 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336703, d337691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336703, d337691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d336680 q = 1) (hb : d337668 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336680, d337668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336680, d337668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92022 q ha hb
  have h15 (q : Pattern) (ha : d336481 q = 1) (hb : d337477 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336481, d337477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92022 q ha hb
    | true =>
      simp only [d336481, d337477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d336681 q = 1) (hb : d337669 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336681, d337669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d336681, d337669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d336482 q = 1) (hb : d337478 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336482, d337478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d336482, d337478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d336682 q = 1) (hb : d337670 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336682, d337670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d336682, d337670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d336683 q = 1) (hb : d337671 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336683, d337671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d336683, d337671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d336689 q = 1) (hb : d337677 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336689, d337677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d336689, d337677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d336704 q = 1) (hb : d337692 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336704, d337692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d336704, d337692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro92065 (p : Pattern) (ha : d336714 p = 1) (hb : d337697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336699 q = 1) (hb : d337687 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336699, d337687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336699, d337687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92025 q ha hb
  have h2 (q : Pattern) (ha : d336496 q = 1) (hb : d337492 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336496, d337492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92025 q ha hb
    | true =>
      simp only [d336496, d337492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336700 q = 1) (hb : d337688 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336700, d337688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336700, d337688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336497 q = 1) (hb : d337493 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336497, d337493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336497, d337493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336701 q = 1) (hb : d337689 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336701, d337689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336701, d337689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336702 q = 1) (hb : d337690 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336702, d337690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336702, d337690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336708 q = 1) (hb : d337696 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336708, d337696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336708, d337696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d1883 q = 1) (hb : d336709 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1883, d336709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1883, d336709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92027 q ha hb
  have h9 (q : Pattern) (ha : d1597 q = 1) (hb : d336508 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1597, d336508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92027 q ha hb
    | true =>
      simp only [d1597, d336508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1884 q = 1) (hb : d336710 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1884, d336710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1884, d336710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1598 q = 1) (hb : d336509 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1598, d336509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1598, d336509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1885 q = 1) (hb : d336711 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1885, d336711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1885, d336711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1886 q = 1) (hb : d336712 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1886, d336712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1886, d336712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d1887 q = 1) (hb : d336713 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1887, d336713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1887, d336713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d336714 q = 1) (hb : d337697 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336714, d337697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336714, d337697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro92066 (p : Pattern) (ha : d336720 p = 1) (hb : d337703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336686 q = 1) (hb : d337674 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336686, d337674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336686, d337674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92062 q ha hb
  have h2 (q : Pattern) (ha : d336687 q = 1) (hb : d337675 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336687, d337675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336687, d337675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336688 q = 1) (hb : d337676 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336688, d337676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336688, d337676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336691 q = 1) (hb : d337679 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336691, d337679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92062 q ha hb
    | true =>
      simp only [d336691, d337679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92063 q ha hb
  have h5 (q : Pattern) (ha : d336692 q = 1) (hb : d337680 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336692, d337680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336692, d337680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336693 q = 1) (hb : d337681 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336693, d337681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336693, d337681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336694 q = 1) (hb : d337682 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336694, d337682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336694, d337682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336705 q = 1) (hb : d337693 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336705, d337693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92062 q ha hb
    | true =>
      simp only [d336705, d337693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92064 q ha hb
  have h9 (q : Pattern) (ha : d336706 q = 1) (hb : d337694 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336706, d337694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336706, d337694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336707 q = 1) (hb : d337695 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336707, d337695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336707, d337695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d336715 q = 1) (hb : d337698 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336715, d337698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92064 q ha hb
    | true =>
      simp only [d336715, d337698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92065 q ha hb
  have h12 (q : Pattern) (ha : d336716 q = 1) (hb : d337699 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336716, d337699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336716, d337699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d336717 q = 1) (hb : d337700 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336717, d337700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336717, d337700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d336718 q = 1) (hb : d337701 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336718, d337701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336718, d337701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d336719 q = 1) (hb : d337702 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d336719, d337702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336719, d337702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d336720 q = 1) (hb : d337703 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d336720, d337703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d336720, d337703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro92067 (p : Pattern) (ha : d336725 p = 1) (hb : d337708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336705 q = 1) (hb : d337693 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336705, d337693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92062 q ha hb
    | true =>
      simp only [d336705, d337693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92064 q ha hb
  have h2 (q : Pattern) (ha : d336706 q = 1) (hb : d337694 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336706, d337694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336706, d337694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336707 q = 1) (hb : d337695 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336707, d337695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336707, d337695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336715 q = 1) (hb : d337698 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336715, d337698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92064 q ha hb
    | true =>
      simp only [d336715, d337698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92065 q ha hb
  have h5 (q : Pattern) (ha : d336716 q = 1) (hb : d337699 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336716, d337699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336716, d337699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336717 q = 1) (hb : d337700 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336717, d337700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336717, d337700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336718 q = 1) (hb : d337701 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336718, d337701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336718, d337701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336723 q = 1) (hb : d337706 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336723, d337706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336723, d337706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d336724 q = 1) (hb : d337707 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d336724, d337707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336724, d337707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336725 q = 1) (hb : d337708 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d336725, d337708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d336725, d337708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro92068 (p : Pattern) (ha : d336731 p = 1) (hb : d337714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336721 q = 1) (hb : d337704 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336721, d337704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92066 q ha hb
    | true =>
      simp only [d336721, d337704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336722 q = 1) (hb : d337705 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336722, d337705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336722, d337705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336726 q = 1) (hb : d337709 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336726, d337709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92067 q ha hb
    | true =>
      simp only [d336726, d337709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336727 q = 1) (hb : d337710 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336727, d337710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336727, d337710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336728 q = 1) (hb : d337711 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336728, d337711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336728, d337711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336729 q = 1) (hb : d337712 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336729, d337712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336729, d337712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336730 q = 1) (hb : d337713 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336730, d337713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336730, d337713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336731 q = 1) (hb : d337714 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336731, d337714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336731, d337714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro92069 (p : Pattern) (ha : d336733 p = 1) (hb : d337716 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336715 q = 1) (hb : d337698 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336715, d337698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92064 q ha hb
    | true =>
      simp only [d336715, d337698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92065 q ha hb
  have h2 (q : Pattern) (ha : d336716 q = 1) (hb : d337699 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336716, d337699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336716, d337699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336717 q = 1) (hb : d337700 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336717, d337700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336717, d337700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336723 q = 1) (hb : d337706 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336723, d337706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336723, d337706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336732 q = 1) (hb : d337715 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d336732, d337715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336732, d337715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336733 q = 1) (hb : d337716 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d336733, d337716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336733, d337716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92070 (p : Pattern) (ha : d336739 p = 1) (hb : d337722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336726 q = 1) (hb : d337709 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336726, d337709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92067 q ha hb
    | true =>
      simp only [d336726, d337709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336727 q = 1) (hb : d337710 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336727, d337710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336727, d337710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336734 q = 1) (hb : d337717 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336734, d337717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92069 q ha hb
    | true =>
      simp only [d336734, d337717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336735 q = 1) (hb : d337718 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336735, d337718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336735, d337718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336736 q = 1) (hb : d337719 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336736, d337719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336736, d337719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336737 q = 1) (hb : d337720 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336737, d337720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336737, d337720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336738 q = 1) (hb : d337721 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336738, d337721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336738, d337721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336739 q = 1) (hb : d337722 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336739, d337722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336739, d337722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro92071 (p : Pattern) (ha : d336752 p = 1) (hb : d337730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336695 q = 1) (hb : d337683 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336695, d337683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336695, d337683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92024 q ha hb
  have h2 (q : Pattern) (ha : d336491 q = 1) (hb : d337487 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336491, d337487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92024 q ha hb
    | true =>
      simp only [d336491, d337487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336696 q = 1) (hb : d337684 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336696, d337684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336696, d337684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336492 q = 1) (hb : d337488 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336492, d337488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336492, d337488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336697 q = 1) (hb : d337685 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336697, d337685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336697, d337685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336698 q = 1) (hb : d337686 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336698, d337686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336698, d337686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336699 q = 1) (hb : d337687 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336699, d337687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336699, d337687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92025 q ha hb
  have h8 (q : Pattern) (ha : d336496 q = 1) (hb : d337492 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336496, d337492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92025 q ha hb
    | true =>
      simp only [d336496, d337492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d336700 q = 1) (hb : d337688 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336700, d337688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336700, d337688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336497 q = 1) (hb : d337493 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336497, d337493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d336497, d337493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d336701 q = 1) (hb : d337689 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336701, d337689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d336701, d337689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d336702 q = 1) (hb : d337690 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336702, d337690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d336702, d337690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d336703 q = 1) (hb : d337691 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336703, d337691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336703, d337691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d336747 q = 1) (hb : d337725 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336747, d337725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336747, d337725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92044 q ha hb
  have h15 (q : Pattern) (ha : d336592 q = 1) (hb : d337580 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336592, d337580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92044 q ha hb
    | true =>
      simp only [d336592, d337580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d336748 q = 1) (hb : d337726 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336748, d337726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d336748, d337726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d336593 q = 1) (hb : d337581 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336593, d337581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d336593, d337581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d336749 q = 1) (hb : d337727 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336749, d337727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d336749, d337727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d336750 q = 1) (hb : d337728 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336750, d337728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d336750, d337728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d336751 q = 1) (hb : d337729 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336751, d337729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d336751, d337729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d336752 q = 1) (hb : d337730 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336752, d337730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d336752, d337730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro92072 (p : Pattern) (ha : d336758 p = 1) (hb : d337736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336753 q = 1) (hb : d337731 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336753, d337731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336753, d337731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92046 q ha hb
  have h2 (q : Pattern) (ha : d336599 q = 1) (hb : d337587 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336599, d337587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92046 q ha hb
    | true =>
      simp only [d336599, d337587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336754 q = 1) (hb : d337732 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336754, d337732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336754, d337732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336600 q = 1) (hb : d337588 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336600, d337588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336600, d337588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336755 q = 1) (hb : d337733 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336755, d337733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336755, d337733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336756 q = 1) (hb : d337734 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336756, d337734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336756, d337734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336757 q = 1) (hb : d337735 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336757, d337735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336757, d337735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336758 q = 1) (hb : d337736 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336758, d337736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336758, d337736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro92073 (p : Pattern) (ha : d336764 p = 1) (hb : d337742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336705 q = 1) (hb : d337693 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336705, d337693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92062 q ha hb
    | true =>
      simp only [d336705, d337693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92064 q ha hb
  have h2 (q : Pattern) (ha : d336706 q = 1) (hb : d337694 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336706, d337694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336706, d337694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336707 q = 1) (hb : d337695 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336707, d337695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336707, d337695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336715 q = 1) (hb : d337698 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336715, d337698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92064 q ha hb
    | true =>
      simp only [d336715, d337698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92065 q ha hb
  have h5 (q : Pattern) (ha : d336716 q = 1) (hb : d337699 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336716, d337699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336716, d337699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336717 q = 1) (hb : d337700 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336717, d337700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336717, d337700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336718 q = 1) (hb : d337701 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336718, d337701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336718, d337701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336759 q = 1) (hb : d337737 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336759, d337737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92071 q ha hb
    | true =>
      simp only [d336759, d337737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92072 q ha hb
  have h9 (q : Pattern) (ha : d336760 q = 1) (hb : d337738 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336760, d337738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336760, d337738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336761 q = 1) (hb : d337739 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336761, d337739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336761, d337739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d336762 q = 1) (hb : d337740 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336762, d337740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336762, d337740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d336763 q = 1) (hb : d337741 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d336763, d337741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336763, d337741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d336764 q = 1) (hb : d337742 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d336764, d337742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d336764, d337742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro92074 (p : Pattern) (ha : d336770 p = 1) (hb : d337748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336765 q = 1) (hb : d337743 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336765, d337743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92073 q ha hb
    | true =>
      simp only [d336765, d337743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336766 q = 1) (hb : d337744 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336766, d337744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336766, d337744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336767 q = 1) (hb : d337745 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336767, d337745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336767, d337745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336768 q = 1) (hb : d337746 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336768, d337746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336768, d337746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336769 q = 1) (hb : d337747 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336769, d337747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336769, d337747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336770 q = 1) (hb : d337748 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336770, d337748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336770, d337748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92075 (p : Pattern) (ha : d336776 p = 1) (hb : d337754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336740 q = 1) (hb : d337723 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336740, d337723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92068 q ha hb
    | true =>
      simp only [d336740, d337723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92070 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d336745 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d336746 q = 1) (hb : d337724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336746, d337724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336746, d337724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d336771 q = 1) (hb : d337749 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336771, d337749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92074 q ha hb
    | true =>
      simp only [d336771, d337749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336772 q = 1) (hb : d337750 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336772, d337750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336772, d337750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336773 q = 1) (hb : d337751 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336773, d337751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336773, d337751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336774 q = 1) (hb : d337752 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336774, d337752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336774, d337752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336775 q = 1) (hb : d337753 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336775, d337753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336775, d337753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d336776 q = 1) (hb : d337754 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336776, d337754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336776, d337754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro92076 (p : Pattern) (ha : d336744 p = 1) (hb : d337759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336734 q = 1) (hb : d337717 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336734, d337717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92069 q ha hb
    | true =>
      simp only [d336734, d337717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336735 q = 1) (hb : d337718 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336735, d337718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336735, d337718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336741 q = 1) (hb : d337756 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336741, d337756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336741, d337756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336742 q = 1) (hb : d337757 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336742, d337757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336742, d337757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336743 q = 1) (hb : d337758 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336743, d337758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336743, d337758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336744 q = 1) (hb : d337759 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336744, d337759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336744, d337759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92077 (p : Pattern) (ha : d336783 p = 1) (hb : d337765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336778 q = 1) (hb : d337760 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336778, d337760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92076 q ha hb
    | true =>
      simp only [d336778, d337760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336779 q = 1) (hb : d337761 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336779, d337761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336779, d337761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336780 q = 1) (hb : d337762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336780, d337762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336780, d337762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336781 q = 1) (hb : d337763 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336781, d337763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336781, d337763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336782 q = 1) (hb : d337764 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336782, d337764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336782, d337764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336783 q = 1) (hb : d337765 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336783, d337765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336783, d337765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92078 (p : Pattern) (ha : d336789 p = 1) (hb : d337771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336541 q = 1) (hb : d337531 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336541, d337531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336541, d337531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92033 q ha hb
  have h2 (q : Pattern) (ha : d336542 q = 1) (hb : d337532 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336542, d337532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336542, d337532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336551 q = 1) (hb : d337541 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336551, d337541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92033 q ha hb
    | true =>
      simp only [d336551, d337541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92036 q ha hb
  have h4 (q : Pattern) (ha : d336552 q = 1) (hb : d337542 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336552, d337542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336552, d337542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336553 q = 1) (hb : d337543 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d336553, d337543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336553, d337543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336644 q = 1) (hb : d337632 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336644, d337632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92050 q ha hb
    | true =>
      simp only [d336644, d337632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92057 q ha hb
  have h7 (q : Pattern) (ha : d336657 q = 1) (hb : d337645 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336657, d337645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92058 q ha hb
    | true =>
      simp only [d336657, d337645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92059 q ha hb
  have h8 (q : Pattern) (ha : d336658 q = 1) (hb : d337646 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336658, d337646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336658, d337646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d336659 q = 1) (hb : d337647 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d336659, d337647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d336659, d337647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d336660 q = 1) (hb : d337648 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d336660, d337648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336660, d337648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d336664 q = 1) (hb : d337652 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336664, d337652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336664, d337652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92060 q ha hb
  have h12 (q : Pattern) (ha : d336666 q = 1) (hb : d337654 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336666, d337654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336666, d337654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92061 q ha hb
  have h13 (q : Pattern) (ha : d336667 q = 1) (hb : d337655 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336667, d337655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d336667, d337655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d336668 q = 1) (hb : d337656 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d336668, d337656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d336668, d337656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d336669 q = 1) (hb : d337657 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d336669, d337657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d336669, d337657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d336670 q = 1) (hb : d337658 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d336670, d337658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336670, d337658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d336777 q = 1) (hb : d337755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336777, d337755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336777, d337755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92075 q ha hb
  have h18 (q : Pattern) (ha : d336784 q = 1) (hb : d337766 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336784, d337766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336784, d337766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92077 q ha hb
  have h19 (q : Pattern) (ha : d336785 q = 1) (hb : d337767 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336785, d337767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d336785, d337767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d336786 q = 1) (hb : d337768 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d336786, d337768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d336786, d337768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d336787 q = 1) (hb : d337769 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d336787, d337769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d336787, d337769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d336788 q = 1) (hb : d337770 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d336788, d337770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d336788, d337770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d336789 q = 1) (hb : d337771 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d336789, d337771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d336789, d337771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro92079 (p : Pattern) (ha : d336795 p = 1) (hb : d337777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336790 q = 1) (hb : d337772 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d336790, d337772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336790, d337772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92078 q ha hb
  have h2 (q : Pattern) (ha : d336791 q = 1) (hb : d337773 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d336791, d337773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336791, d337773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336792 q = 1) (hb : d337774 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d336792, d337774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336792, d337774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336793 q = 1) (hb : d337775 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d336793, d337775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336793, d337775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336794 q = 1) (hb : d337776 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d336794, d337776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336794, d337776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336795 q = 1) (hb : d337777 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d336795, d337777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336795, d337777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92080 (p : Pattern) (ha : d336803 p = 1) (hb : d337782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53319 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2058 q = 1) (hb : d53319 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53321 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2043 q = 1) (hb : d53321 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
  have h5 (q : Pattern) (ha : d2059 q = 1) (hb : d336800 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, d336800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2059, d336800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2076 q = 1) (hb : d336801 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2076, d336801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2076, d336801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d336801 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2077 q = 1) (hb : d336801 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2078 q = 1) (hb : d336802 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2078, d336802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2078, d336802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d336803 q = 1) (hb : d337782 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d336803, d337782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336803, d337782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro92081 (p : Pattern) (ha : d336809 p = 1) (hb : d337788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336804 q = 1) (hb : d337783 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336804, d337783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92080 q ha hb
    | true =>
      simp only [d336804, d337783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336805 q = 1) (hb : d337784 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336805, d337784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336805, d337784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336806 q = 1) (hb : d337785 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336806, d337785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336806, d337785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336807 q = 1) (hb : d337786 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336807, d337786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336807, d337786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336808 q = 1) (hb : d337787 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336808, d337787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336808, d337787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336809 q = 1) (hb : d337788 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336809, d337788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336809, d337788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92082 (p : Pattern) (ha : d336813 p = 1) (hb : d337791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53325 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5238 q = 1) (hb : d53325 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h3 (q : Pattern) (ha : d5239 q = 1) (hb : d336810 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d336810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5239, d336810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d207147 q = 1) (hb : d336811 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d207147, d336811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207147, d336811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d336811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d336811 q = 1) (hb : d337789 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d337789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d337789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d336812 q = 1) (hb : d337790 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d336812, d337790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336812, d337790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336813 q = 1) (hb : d337791 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d336813, d337791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336813, d337791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92083 (p : Pattern) (ha : d336818 p = 1) (hb : d337796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53325 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5238 q = 1) (hb : d53325 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h3 (q : Pattern) (ha : d5239 q = 1) (hb : d336810 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d336810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5239, d336810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d207147 q = 1) (hb : d336811 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d207147, d336811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207147, d336811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d336811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d336811 q = 1) (hb : d337789 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d337789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d337789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d336812 q = 1) (hb : d337790 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d336812, d337790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336812, d337790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53319 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2058 q = 1) (hb : d53319 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53321 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2043 q = 1) (hb : d53321 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
  have h12 (q : Pattern) (ha : d2059 q = 1) (hb : d336800 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, d336800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2059, d336800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2076 q = 1) (hb : d336801 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2076, d336801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2076, d336801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d336801 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d2077 q = 1) (hb : d336801 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2078 q = 1) (hb : d336802 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2078, d336802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d2078, d336802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d336818 q = 1) (hb : d337796 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d336818, d337796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336818, d337796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro92084 (p : Pattern) (ha : d336825 p = 1) (hb : d337803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336814 q = 1) (hb : d337792 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336814, d337792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92082 q ha hb
    | true =>
      simp only [d336814, d337792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336815 q = 1) (hb : d337793 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336815, d337793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336815, d337793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336816 q = 1) (hb : d337794 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336816, d337794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336816, d337794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336817 q = 1) (hb : d337795 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336817, d337795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336817, d337795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336819 q = 1) (hb : d337797 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336819, d337797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92083 q ha hb
    | true =>
      simp only [d336819, d337797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336820 q = 1) (hb : d337798 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336820, d337798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336820, d337798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336821 q = 1) (hb : d337799 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336821, d337799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336821, d337799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336822 q = 1) (hb : d337800 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336822, d337800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336822, d337800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d336823 q = 1) (hb : d337801 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336823, d337801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336823, d337801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336804 q = 1) (hb : d337783 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336804, d337783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92080 q ha hb
    | true =>
      simp only [d336804, d337783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d336805 q = 1) (hb : d337784 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336805, d337784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336805, d337784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d336806 q = 1) (hb : d337785 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336806, d337785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336806, d337785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d336807 q = 1) (hb : d337786 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336807, d337786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d336807, d337786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d336824 q = 1) (hb : d337802 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336824, d337802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d336824, d337802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d336825 q = 1) (hb : d337803 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336825, d337803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d336825, d337803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro92085 (p : Pattern) (ha : d2079 p = 1) (hb : d336830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53319 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2058 q = 1) (hb : d53319 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53321 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2043 q = 1) (hb : d53321 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
  have h4 (q : Pattern) (ha : d2059 q = 1) (hb : d336800 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, d336800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2059, d336800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2076 q = 1) (hb : d336801 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2076, d336801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2076, d336801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d336801 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2077 q = 1) (hb : d336801 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2078 q = 1) (hb : d336802 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2078, d336802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2078, d336802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h10 (q : Pattern) (ha : d2079 q = 1) (hb : d336830 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d2079, d336830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2079, d336830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h10 p ha hb
theorem andIntro92086 (p : Pattern) (ha : d336836 p = 1) (hb : d337808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336819 q = 1) (hb : d337797 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336819, d337797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92083 q ha hb
    | true =>
      simp only [d336819, d337797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336820 q = 1) (hb : d337798 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336820, d337798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336820, d337798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336821 q = 1) (hb : d337799 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336821, d337799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336821, d337799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336822 q = 1) (hb : d337800 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336822, d337800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336822, d337800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336829 q = 1) (hb : d337807 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336829, d337807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336829, d337807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d2080 q = 1) (hb : d336831 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2080, d336831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92085 q ha hb
    | true =>
      simp only [d2080, d336831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2081 q = 1) (hb : d336832 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2081, d336832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2081, d336832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2082 q = 1) (hb : d336833 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2082, d336833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2082, d336833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2083 q = 1) (hb : d336834 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2083, d336834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2083, d336834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2084 q = 1) (hb : d336835 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2084, d336835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2084, d336835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d336836 q = 1) (hb : d337808 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336836, d337808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336836, d337808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro92087 (p : Pattern) (ha : d336843 p = 1) (hb : d337815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336826 q = 1) (hb : d337804 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336826, d337804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92081 q ha hb
    | true =>
      simp only [d336826, d337804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92084 q ha hb
  have h2 (q : Pattern) (ha : d336827 q = 1) (hb : d337805 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336827, d337805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336827, d337805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336828 q = 1) (hb : d337806 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336828, d337806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336828, d337806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336837 q = 1) (hb : d337809 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336837, d337809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92084 q ha hb
    | true =>
      simp only [d336837, d337809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92086 q ha hb
  have h5 (q : Pattern) (ha : d336838 q = 1) (hb : d337810 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336838, d337810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336838, d337810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336839 q = 1) (hb : d337811 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336839, d337811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336839, d337811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336840 q = 1) (hb : d337812 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336840, d337812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336840, d337812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336841 q = 1) (hb : d337813 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336841, d337813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336841, d337813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d336842 q = 1) (hb : d337814 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d336842, d337814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336842, d337814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336843 q = 1) (hb : d337815 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d336843, d337815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d336843, d337815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro92088 (p : Pattern) (ha : d336847 p = 1) (hb : d337819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336837 q = 1) (hb : d337809 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336837, d337809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92084 q ha hb
    | true =>
      simp only [d336837, d337809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92086 q ha hb
  have h2 (q : Pattern) (ha : d336838 q = 1) (hb : d337810 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336838, d337810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336838, d337810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336839 q = 1) (hb : d337811 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336839, d337811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336839, d337811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336841 q = 1) (hb : d337813 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336841, d337813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336841, d337813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336846 q = 1) (hb : d337818 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d336846, d337818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336846, d337818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336847 q = 1) (hb : d337819 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d336847, d337819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336847, d337819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92089 (p : Pattern) (ha : d336853 p = 1) (hb : d337825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336844 q = 1) (hb : d337816 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336844, d337816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92087 q ha hb
    | true =>
      simp only [d336844, d337816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336845 q = 1) (hb : d337817 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336845, d337817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336845, d337817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336848 q = 1) (hb : d337820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92088 q ha hb
    | true =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336849 q = 1) (hb : d337821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336850 q = 1) (hb : d337822 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336850, d337822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336850, d337822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336851 q = 1) (hb : d337823 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336851, d337823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336851, d337823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336852 q = 1) (hb : d337824 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336852, d337824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336852, d337824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336853 q = 1) (hb : d337825 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336853, d337825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336853, d337825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92090 (p : Pattern) (ha : d336857 p = 1) (hb : d337829 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336848 q = 1) (hb : d337820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92088 q ha hb
    | true =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336849 q = 1) (hb : d337821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336854 q = 1) (hb : d337826 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336854, d337826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336854, d337826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336855 q = 1) (hb : d337827 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336855, d337827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336855, d337827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336856 q = 1) (hb : d337828 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336856, d337828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336856, d337828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336857 q = 1) (hb : d337829 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336857, d337829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336857, d337829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92091 (p : Pattern) (ha : d336863 p = 1) (hb : d337835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336858 q = 1) (hb : d337830 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336858, d337830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92089 q ha hb
    | true =>
      simp only [d336858, d337830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92090 q ha hb
  have h2 (q : Pattern) (ha : d336859 q = 1) (hb : d337831 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336859, d337831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336859, d337831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336860 q = 1) (hb : d337832 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336860, d337832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336860, d337832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336861 q = 1) (hb : d337833 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336861, d337833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336861, d337833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336862 q = 1) (hb : d337834 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336862, d337834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336862, d337834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336863 q = 1) (hb : d337835 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336863, d337835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336863, d337835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92092 (p : Pattern) (ha : d336866 p = 1) (hb : d337838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336844 q = 1) (hb : d337816 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336844, d337816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92087 q ha hb
    | true =>
      simp only [d336844, d337816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336845 q = 1) (hb : d337817 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336845, d337817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336845, d337817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336848 q = 1) (hb : d337820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92088 q ha hb
    | true =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336849 q = 1) (hb : d337821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336850 q = 1) (hb : d337822 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336850, d337822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336850, d337822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336851 q = 1) (hb : d337823 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336851, d337823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336851, d337823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336852 q = 1) (hb : d337824 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336852, d337824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336852, d337824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336866 q = 1) (hb : d337838 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336866, d337838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336866, d337838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro92093 (p : Pattern) (ha : d336867 p = 1) (hb : d337839 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336848 q = 1) (hb : d337820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92088 q ha hb
    | true =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336849 q = 1) (hb : d337821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336854 q = 1) (hb : d337826 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336854, d337826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336854, d337826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336855 q = 1) (hb : d337827 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336855, d337827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336855, d337827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336856 q = 1) (hb : d337828 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336856, d337828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336856, d337828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336867 q = 1) (hb : d337839 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336867, d337839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336867, d337839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92094 (p : Pattern) (ha : d336873 p = 1) (hb : d337845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336858 q = 1) (hb : d337830 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336858, d337830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92089 q ha hb
    | true =>
      simp only [d336858, d337830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92090 q ha hb
  have h2 (q : Pattern) (ha : d336859 q = 1) (hb : d337831 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336859, d337831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336859, d337831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336860 q = 1) (hb : d337832 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336860, d337832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336860, d337832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336861 q = 1) (hb : d337833 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336861, d337833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336861, d337833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336862 q = 1) (hb : d337834 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336862, d337834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336862, d337834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336868 q = 1) (hb : d337840 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336868, d337840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92092 q ha hb
    | true =>
      simp only [d336868, d337840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92093 q ha hb
  have h7 (q : Pattern) (ha : d336869 q = 1) (hb : d337841 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336869, d337841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336869, d337841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336870 q = 1) (hb : d337842 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336870, d337842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336870, d337842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d336871 q = 1) (hb : d337843 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336871, d337843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336871, d337843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336872 q = 1) (hb : d337844 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336872, d337844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336872, d337844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d336873 q = 1) (hb : d337845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336873, d337845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336873, d337845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro92095 (p : Pattern) (ha : d336878 p = 1) (hb : d337850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336844 q = 1) (hb : d337816 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336844, d337816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92087 q ha hb
    | true =>
      simp only [d336844, d337816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336845 q = 1) (hb : d337817 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336845, d337817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336845, d337817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336848 q = 1) (hb : d337820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92088 q ha hb
    | true =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336849 q = 1) (hb : d337821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336850 q = 1) (hb : d337822 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336850, d337822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336850, d337822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336851 q = 1) (hb : d337823 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336851, d337823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336851, d337823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336877 q = 1) (hb : d337849 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336877, d337849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336877, d337849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336878 q = 1) (hb : d337850 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336878, d337850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336878, d337850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92096 (p : Pattern) (ha : d336880 p = 1) (hb : d337852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336848 q = 1) (hb : d337820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92088 q ha hb
    | true =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336849 q = 1) (hb : d337821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336854 q = 1) (hb : d337826 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336854, d337826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336854, d337826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336855 q = 1) (hb : d337827 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336855, d337827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336855, d337827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336879 q = 1) (hb : d337851 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336879, d337851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336879, d337851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336880 q = 1) (hb : d337852 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336880, d337852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336880, d337852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92097 (p : Pattern) (ha : d336887 p = 1) (hb : d337859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336844 q = 1) (hb : d337816 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336844, d337816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92087 q ha hb
    | true =>
      simp only [d336844, d337816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336845 q = 1) (hb : d337817 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336845, d337817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336845, d337817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336848 q = 1) (hb : d337820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92088 q ha hb
    | true =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336849 q = 1) (hb : d337821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336850 q = 1) (hb : d337822 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336850, d337822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336850, d337822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336885 q = 1) (hb : d337857 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336885, d337857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336885, d337857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336886 q = 1) (hb : d337858 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336886, d337858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336886, d337858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336887 q = 1) (hb : d337859 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336887, d337859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336887, d337859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92098 (p : Pattern) (ha : d336890 p = 1) (hb : d337862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336848 q = 1) (hb : d337820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92088 q ha hb
    | true =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336849 q = 1) (hb : d337821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336854 q = 1) (hb : d337826 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336854, d337826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336854, d337826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336888 q = 1) (hb : d337860 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336888, d337860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336888, d337860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336889 q = 1) (hb : d337861 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336889, d337861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336889, d337861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336890 q = 1) (hb : d337862 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336890, d337862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336890, d337862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92099 (p : Pattern) (ha : d336897 p = 1) (hb : d337869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336804 q = 1) (hb : d337783 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336804, d337783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92080 q ha hb
    | true =>
      simp only [d336804, d337783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336805 q = 1) (hb : d337784 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336805, d337784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336805, d337784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336806 q = 1) (hb : d337785 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336806, d337785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336806, d337785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336807 q = 1) (hb : d337786 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336807, d337786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336807, d337786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336808 q = 1) (hb : d337787 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336808, d337787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336808, d337787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336824 q = 1) (hb : d337802 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336824, d337802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336824, d337802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336897 q = 1) (hb : d337869 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336897, d337869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336897, d337869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro92100 (p : Pattern) (ha : d336903 p = 1) (hb : d337875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336894 q = 1) (hb : d337866 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336894, d337866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336894, d337866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92081 q ha hb
  have h2 (q : Pattern) (ha : d336895 q = 1) (hb : d337867 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336895, d337867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336895, d337867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336896 q = 1) (hb : d337868 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336896, d337868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336896, d337868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336898 q = 1) (hb : d337870 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336898, d337870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92081 q ha hb
    | true =>
      simp only [d336898, d337870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92099 q ha hb
  have h5 (q : Pattern) (ha : d336899 q = 1) (hb : d337871 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336899, d337871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336899, d337871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336900 q = 1) (hb : d337872 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336900, d337872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336900, d337872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336901 q = 1) (hb : d337873 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336901, d337873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336901, d337873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336826 q = 1) (hb : d337804 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336826, d337804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92081 q ha hb
    | true =>
      simp only [d336826, d337804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92084 q ha hb
  have h9 (q : Pattern) (ha : d336827 q = 1) (hb : d337805 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336827, d337805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336827, d337805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336828 q = 1) (hb : d337806 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336828, d337806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336828, d337806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d336837 q = 1) (hb : d337809 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336837, d337809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92084 q ha hb
    | true =>
      simp only [d336837, d337809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92086 q ha hb
  have h12 (q : Pattern) (ha : d336838 q = 1) (hb : d337810 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336838, d337810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336838, d337810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d336839 q = 1) (hb : d337811 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336839, d337811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336839, d337811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d336840 q = 1) (hb : d337812 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336840, d337812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336840, d337812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d336902 q = 1) (hb : d337874 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d336902, d337874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336902, d337874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d336903 q = 1) (hb : d337875 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d336903, d337875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d336903, d337875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro92101 (p : Pattern) (ha : d336909 p = 1) (hb : d337881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336904 q = 1) (hb : d337876 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336904, d337876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92100 q ha hb
    | true =>
      simp only [d336904, d337876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336905 q = 1) (hb : d337877 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336905, d337877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336905, d337877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336844 q = 1) (hb : d337816 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336844, d337816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92087 q ha hb
    | true =>
      simp only [d336844, d337816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336845 q = 1) (hb : d337817 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336845, d337817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336845, d337817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336906 q = 1) (hb : d337878 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336906, d337878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336906, d337878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336907 q = 1) (hb : d337879 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336907, d337879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336907, d337879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336908 q = 1) (hb : d337880 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336908, d337880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336908, d337880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336909 q = 1) (hb : d337881 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336909, d337881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336909, d337881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92102 (p : Pattern) (ha : d336914 p = 1) (hb : d337884 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53325 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5238 q = 1) (hb : d53325 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h3 (q : Pattern) (ha : d5239 q = 1) (hb : d336810 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d336810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5239, d336810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27181 q = 1) (hb : d336912 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d27181, d336912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27181, d336912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d336912 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d239849 q = 1) (hb : d336912 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d239849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d239850 q = 1) (hb : d336913 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d239850, d336913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d239850, d336913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d336914 q = 1) (hb : d337884 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d336914, d337884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336914, d337884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro92103 (p : Pattern) (ha : d336920 p = 1) (hb : d337890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336814 q = 1) (hb : d337792 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336814, d337792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92082 q ha hb
    | true =>
      simp only [d336814, d337792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336815 q = 1) (hb : d337793 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336815, d337793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336815, d337793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336816 q = 1) (hb : d337794 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336816, d337794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336816, d337794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336817 q = 1) (hb : d337795 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336817, d337795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336817, d337795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336819 q = 1) (hb : d337797 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336819, d337797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92083 q ha hb
    | true =>
      simp only [d336819, d337797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336820 q = 1) (hb : d337798 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336820, d337798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336820, d337798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336821 q = 1) (hb : d337799 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336821, d337799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336821, d337799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336822 q = 1) (hb : d337800 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336822, d337800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336822, d337800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d336823 q = 1) (hb : d337801 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336823, d337801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336823, d337801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336915 q = 1) (hb : d337885 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336915, d337885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92102 q ha hb
    | true =>
      simp only [d336915, d337885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d336916 q = 1) (hb : d337886 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336916, d337886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336916, d337886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d336917 q = 1) (hb : d337887 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336917, d337887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336917, d337887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d336918 q = 1) (hb : d337888 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336918, d337888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d336918, d337888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d336919 q = 1) (hb : d337889 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336919, d337889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d336919, d337889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d336920 q = 1) (hb : d337890 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336920, d337890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d336920, d337890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro92104 (p : Pattern) (ha : d336921 p = 1) (hb : d337891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53325 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5238 q = 1) (hb : d53325 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h3 (q : Pattern) (ha : d5239 q = 1) (hb : d336810 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d336810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5239, d336810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d207147 q = 1) (hb : d336811 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d207147, d336811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207147, d336811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d336811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d336811 q = 1) (hb : d337789 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d337789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d337789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d336812 q = 1) (hb : d337790 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d336812, d337790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336812, d337790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d27181 q = 1) (hb : d336912 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d27181, d336912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27181, d336912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d336912 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d239849 q = 1) (hb : d336912 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d239849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d239849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d239850 q = 1) (hb : d336913 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d239850, d336913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d239850, d336913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d336921 q = 1) (hb : d337891 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d336921, d337891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336921, d337891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro92105 (p : Pattern) (ha : d336927 p = 1) (hb : d337897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336922 q = 1) (hb : d337892 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336922, d337892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92104 q ha hb
    | true =>
      simp only [d336922, d337892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336923 q = 1) (hb : d337893 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336923, d337893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336923, d337893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336924 q = 1) (hb : d337894 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336924, d337894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336924, d337894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336925 q = 1) (hb : d337895 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336925, d337895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336925, d337895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336926 q = 1) (hb : d337896 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336926, d337896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336926, d337896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336927 q = 1) (hb : d337897 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336927, d337897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336927, d337897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92106 (p : Pattern) (ha : d336933 p = 1) (hb : d337903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336826 q = 1) (hb : d337804 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336826, d337804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92081 q ha hb
    | true =>
      simp only [d336826, d337804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92084 q ha hb
  have h2 (q : Pattern) (ha : d336827 q = 1) (hb : d337805 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336827, d337805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336827, d337805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336828 q = 1) (hb : d337806 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336828, d337806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336828, d337806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336837 q = 1) (hb : d337809 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336837, d337809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92084 q ha hb
    | true =>
      simp only [d336837, d337809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92086 q ha hb
  have h5 (q : Pattern) (ha : d336838 q = 1) (hb : d337810 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336838, d337810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336838, d337810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336839 q = 1) (hb : d337811 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336839, d337811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336839, d337811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336840 q = 1) (hb : d337812 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336840, d337812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336840, d337812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336928 q = 1) (hb : d337898 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d336928, d337898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92103 q ha hb
    | true =>
      simp only [d336928, d337898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92105 q ha hb
  have h9 (q : Pattern) (ha : d336929 q = 1) (hb : d337899 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d336929, d337899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336929, d337899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336930 q = 1) (hb : d337900 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d336930, d337900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336930, d337900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d336931 q = 1) (hb : d337901 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d336931, d337901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336931, d337901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d336932 q = 1) (hb : d337902 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d336932, d337902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336932, d337902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d336933 q = 1) (hb : d337903 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d336933, d337903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d336933, d337903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro92107 (p : Pattern) (ha : d336939 p = 1) (hb : d337909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336934 q = 1) (hb : d337904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336934, d337904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92106 q ha hb
    | true =>
      simp only [d336934, d337904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336935 q = 1) (hb : d337905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336935, d337905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336935, d337905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336936 q = 1) (hb : d337906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336936, d337906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336936, d337906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336937 q = 1) (hb : d337907 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336937, d337907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336937, d337907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336938 q = 1) (hb : d337908 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336938, d337908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336938, d337908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336939 q = 1) (hb : d337909 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336939, d337909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336939, d337909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92108 (p : Pattern) (ha : d336945 p = 1) (hb : d337915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336881 q = 1) (hb : d337853 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336881, d337853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92095 q ha hb
    | true =>
      simp only [d336881, d337853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92096 q ha hb
  have h2 (q : Pattern) (ha : d336882 q = 1) (hb : d337854 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336882, d337854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336882, d337854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336883 q = 1) (hb : d337855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336883, d337855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336883, d337855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336884 q = 1) (hb : d337856 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336884, d337856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336884, d337856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336891 q = 1) (hb : d337863 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336891, d337863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92097 q ha hb
    | true =>
      simp only [d336891, d337863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92098 q ha hb
  have h6 (q : Pattern) (ha : d336892 q = 1) (hb : d337864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336892, d337864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336892, d337864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336893 q = 1) (hb : d337865 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336893, d337865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336893, d337865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336910 q = 1) (hb : d337882 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336910, d337882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92101 q ha hb
    | true =>
      simp only [d336910, d337882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92089 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d336858 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d336911 q = 1) (hb : d337883 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336911, d337883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d336911, d337883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d336940 q = 1) (hb : d337910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336940, d337910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92107 q ha hb
    | true =>
      simp only [d336940, d337910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d336941 q = 1) (hb : d337911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336941, d337911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d336941, d337911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d336942 q = 1) (hb : d337912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336942, d337912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336942, d337912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d336943 q = 1) (hb : d337913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336943, d337913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336943, d337913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d336944 q = 1) (hb : d337914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336944, d337914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336944, d337914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d336945 q = 1) (hb : d337915 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336945, d337915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336945, d337915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro92109 (p : Pattern) (ha : d336946 p = 1) (hb : d337916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336844 q = 1) (hb : d337816 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336844, d337816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92087 q ha hb
    | true =>
      simp only [d336844, d337816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336845 q = 1) (hb : d337817 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336845, d337817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336845, d337817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336848 q = 1) (hb : d337820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92088 q ha hb
    | true =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336849 q = 1) (hb : d337821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336850 q = 1) (hb : d337822 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336850, d337822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336850, d337822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336851 q = 1) (hb : d337823 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336851, d337823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336851, d337823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336877 q = 1) (hb : d337849 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336877, d337849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336877, d337849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336946 q = 1) (hb : d337916 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336946, d337916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336946, d337916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro92110 (p : Pattern) (ha : d336947 p = 1) (hb : d337917 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336848 q = 1) (hb : d337820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92088 q ha hb
    | true =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336849 q = 1) (hb : d337821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336854 q = 1) (hb : d337826 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336854, d337826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336854, d337826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336855 q = 1) (hb : d337827 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336855, d337827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336855, d337827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336879 q = 1) (hb : d337851 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336879, d337851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336879, d337851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336947 q = 1) (hb : d337917 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336947, d337917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336947, d337917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92111 (p : Pattern) (ha : d336952 p = 1) (hb : d337922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336844 q = 1) (hb : d337816 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336844, d337816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92087 q ha hb
    | true =>
      simp only [d336844, d337816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336845 q = 1) (hb : d337817 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336845, d337817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336845, d337817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336848 q = 1) (hb : d337820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92088 q ha hb
    | true =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336849 q = 1) (hb : d337821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336850 q = 1) (hb : d337822 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336850, d337822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336850, d337822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336885 q = 1) (hb : d337857 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336885, d337857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336885, d337857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336886 q = 1) (hb : d337858 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336886, d337858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336886, d337858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336952 q = 1) (hb : d337922 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336952, d337922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336952, d337922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro92112 (p : Pattern) (ha : d336953 p = 1) (hb : d337923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336848 q = 1) (hb : d337820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92088 q ha hb
    | true =>
      simp only [d336848, d337820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336849 q = 1) (hb : d337821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336849, d337821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336854 q = 1) (hb : d337826 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336854, d337826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336854, d337826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336888 q = 1) (hb : d337860 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336888, d337860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336888, d337860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336889 q = 1) (hb : d337861 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336889, d337861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336889, d337861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336953 q = 1) (hb : d337923 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336953, d337923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336953, d337923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92113 (p : Pattern) (ha : d336957 p = 1) (hb : d337927 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336904 q = 1) (hb : d337876 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336904, d337876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92100 q ha hb
    | true =>
      simp only [d336904, d337876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336905 q = 1) (hb : d337877 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336905, d337877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336905, d337877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336844 q = 1) (hb : d337816 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336844, d337816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92087 q ha hb
    | true =>
      simp only [d336844, d337816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336845 q = 1) (hb : d337817 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336845, d337817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336845, d337817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336906 q = 1) (hb : d337878 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336906, d337878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336906, d337878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336907 q = 1) (hb : d337879 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336907, d337879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336907, d337879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336908 q = 1) (hb : d337880 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336908, d337880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336908, d337880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336957 q = 1) (hb : d337927 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336957, d337927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336957, d337927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro92114 (p : Pattern) (ha : d336960 p = 1) (hb : d337930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336934 q = 1) (hb : d337904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d336934, d337904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92106 q ha hb
    | true =>
      simp only [d336934, d337904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336935 q = 1) (hb : d337905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d336935, d337905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336935, d337905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336936 q = 1) (hb : d337906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d336936, d337906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336936, d337906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336937 q = 1) (hb : d337907 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d336937, d337907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336937, d337907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336938 q = 1) (hb : d337908 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d336938, d337908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336938, d337908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336960 q = 1) (hb : d337930 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336960, d337930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336960, d337930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92115 (p : Pattern) (ha : d336966 p = 1) (hb : d337936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336881 q = 1) (hb : d337853 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336881, d337853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92095 q ha hb
    | true =>
      simp only [d336881, d337853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92096 q ha hb
  have h2 (q : Pattern) (ha : d336882 q = 1) (hb : d337854 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336882, d337854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336882, d337854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336883 q = 1) (hb : d337855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336883, d337855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336883, d337855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336884 q = 1) (hb : d337856 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336884, d337856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336884, d337856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336891 q = 1) (hb : d337863 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336891, d337863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92097 q ha hb
    | true =>
      simp only [d336891, d337863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92098 q ha hb
  have h6 (q : Pattern) (ha : d336892 q = 1) (hb : d337864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336892, d337864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336892, d337864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336893 q = 1) (hb : d337865 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336893, d337865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336893, d337865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d336910 q = 1) (hb : d337882 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336910, d337882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92101 q ha hb
    | true =>
      simp only [d336910, d337882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92089 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d336858 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d336911 q = 1) (hb : d337883 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336911, d337883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d336911, d337883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d336940 q = 1) (hb : d337910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336940, d337910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92107 q ha hb
    | true =>
      simp only [d336940, d337910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d336941 q = 1) (hb : d337911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336941, d337911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d336941, d337911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d336942 q = 1) (hb : d337912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336942, d337912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336942, d337912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d336943 q = 1) (hb : d337913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336943, d337913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336943, d337913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d336944 q = 1) (hb : d337914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336944, d337914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336944, d337914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d336948 q = 1) (hb : d337918 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336948, d337918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92109 q ha hb
    | true =>
      simp only [d336948, d337918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92110 q ha hb
  have h17 (q : Pattern) (ha : d336949 q = 1) (hb : d337919 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336949, d337919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336949, d337919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d336950 q = 1) (hb : d337920 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336950, d337920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d336950, d337920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d336951 q = 1) (hb : d337921 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336951, d337921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336951, d337921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d336954 q = 1) (hb : d337924 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336954, d337924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92111 q ha hb
    | true =>
      simp only [d336954, d337924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92112 q ha hb
  have h21 (q : Pattern) (ha : d336955 q = 1) (hb : d337925 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336955, d337925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336955, d337925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d336956 q = 1) (hb : d337926 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336956, d337926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d336956, d337926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d336958 q = 1) (hb : d337928 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336958, d337928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92113 q ha hb
    | true =>
      simp only [d336958, d337928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92092 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d336868 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d336959 q = 1) (hb : d337929 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336959, d337929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d336959, d337929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d336961 q = 1) (hb : d337931 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336961, d337931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92114 q ha hb
    | true =>
      simp only [d336961, d337931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d336962 q = 1) (hb : d337932 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336962, d337932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d336962, d337932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d336963 q = 1) (hb : d337933 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336963, d337933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d336963, d337933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d336964 q = 1) (hb : d337934 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336964, d337934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d336964, d337934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d336965 q = 1) (hb : d337935 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336965, d337935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d336965, d337935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d336966 q = 1) (hb : d337936 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336966, d337936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d336966, d337936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro92116 (p : Pattern) (ha : d336973 p = 1) (hb : d337943 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336858 q = 1) (hb : d337830 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336858, d337830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92089 q ha hb
    | true =>
      simp only [d336858, d337830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92090 q ha hb
  have h2 (q : Pattern) (ha : d336859 q = 1) (hb : d337831 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336859, d337831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336859, d337831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336860 q = 1) (hb : d337832 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336860, d337832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336860, d337832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336861 q = 1) (hb : d337833 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336861, d337833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336861, d337833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336862 q = 1) (hb : d337834 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336862, d337834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336862, d337834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336968 q = 1) (hb : d337938 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336968, d337938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92090 q ha hb
    | true =>
      simp only [d336968, d337938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336969 q = 1) (hb : d337939 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336969, d337939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336969, d337939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336970 q = 1) (hb : d337940 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336970, d337940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336970, d337940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d336971 q = 1) (hb : d337941 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336971, d337941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336971, d337941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336972 q = 1) (hb : d337942 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336972, d337942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336972, d337942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d336973 q = 1) (hb : d337943 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336973, d337943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336973, d337943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro92117 (p : Pattern) (ha : d336979 p = 1) (hb : d337949 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336968 q = 1) (hb : d337938 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336968, d337938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92090 q ha hb
    | true =>
      simp only [d336968, d337938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336969 q = 1) (hb : d337939 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336969, d337939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336969, d337939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336970 q = 1) (hb : d337940 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336970, d337940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336970, d337940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336971 q = 1) (hb : d337941 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336971, d337941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336971, d337941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336972 q = 1) (hb : d337942 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336972, d337942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336972, d337942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336974 q = 1) (hb : d337944 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336974, d337944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92093 q ha hb
    | true =>
      simp only [d336974, d337944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336975 q = 1) (hb : d337945 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336975, d337945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336975, d337945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336976 q = 1) (hb : d337946 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336976, d337946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336976, d337946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d336977 q = 1) (hb : d337947 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336977, d337947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336977, d337947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336978 q = 1) (hb : d337948 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336978, d337948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336978, d337948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d336979 q = 1) (hb : d337949 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336979, d337949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336979, d337949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro92118 (p : Pattern) (ha : d336986 p = 1) (hb : d337956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336958 q = 1) (hb : d337928 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336958, d337928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92113 q ha hb
    | true =>
      simp only [d336958, d337928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92092 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d336868 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d336959 q = 1) (hb : d337929 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336959, d337929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336959, d337929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d336961 q = 1) (hb : d337931 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336961, d337931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92114 q ha hb
    | true =>
      simp only [d336961, d337931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336962 q = 1) (hb : d337932 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336962, d337932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336962, d337932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d336963 q = 1) (hb : d337933 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336963, d337933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336963, d337933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336984 q = 1) (hb : d337954 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336984, d337954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336984, d337954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336985 q = 1) (hb : d337955 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336985, d337955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336985, d337955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d336986 q = 1) (hb : d337956 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336986, d337956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336986, d337956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro92119 (p : Pattern) (ha : d336988 p = 1) (hb : d337958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336974 q = 1) (hb : d337944 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336974, d337944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92093 q ha hb
    | true =>
      simp only [d336974, d337944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d336975 q = 1) (hb : d337945 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336975, d337945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336975, d337945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336976 q = 1) (hb : d337946 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336976, d337946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336976, d337946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d336977 q = 1) (hb : d337947 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336977, d337947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336977, d337947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336978 q = 1) (hb : d337948 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336978, d337948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336978, d337948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336988 q = 1) (hb : d337958 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336988, d337958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336988, d337958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92120 (p : Pattern) (ha : d336999 p = 1) (hb : d337969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336994 q = 1) (hb : d337964 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336994, d337964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336994, d337964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92080 q ha hb
  have h2 (q : Pattern) (ha : d336804 q = 1) (hb : d337783 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336804, d337783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92080 q ha hb
    | true =>
      simp only [d336804, d337783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336995 q = 1) (hb : d337965 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336995, d337965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336995, d337965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336805 q = 1) (hb : d337784 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336805, d337784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336805, d337784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336996 q = 1) (hb : d337966 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336996, d337966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336996, d337966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336997 q = 1) (hb : d337967 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336997, d337967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336997, d337967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336998 q = 1) (hb : d337968 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336998, d337968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336998, d337968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336999 q = 1) (hb : d337969 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d336999, d337969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336999, d337969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92121 (p : Pattern) (ha : d337004 p = 1) (hb : d337974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336994 q = 1) (hb : d337964 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336994, d337964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336994, d337964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92080 q ha hb
  have h2 (q : Pattern) (ha : d336804 q = 1) (hb : d337783 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336804, d337783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92080 q ha hb
    | true =>
      simp only [d336804, d337783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336995 q = 1) (hb : d337965 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336995, d337965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336995, d337965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336805 q = 1) (hb : d337784 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336805, d337784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336805, d337784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336996 q = 1) (hb : d337966 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336996, d337966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336996, d337966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336997 q = 1) (hb : d337967 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336997, d337967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336997, d337967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d336998 q = 1) (hb : d337968 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d336998, d337968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336998, d337968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d337003 q = 1) (hb : d337973 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d337003, d337973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d337003, d337973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d337004 q = 1) (hb : d337974 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d337004, d337974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d337004, d337974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro92122 (p : Pattern) (ha : d337018 p = 1) (hb : d337988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337009 q = 1) (hb : d337979 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d337009, d337979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337009, d337979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92082 q ha hb
  have h2 (q : Pattern) (ha : d336814 q = 1) (hb : d337792 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336814, d337792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92082 q ha hb
    | true =>
      simp only [d336814, d337792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d337010 q = 1) (hb : d337980 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d337010, d337980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337010, d337980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336815 q = 1) (hb : d337793 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336815, d337793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336815, d337793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337011 q = 1) (hb : d337981 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d337011, d337981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337011, d337981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d337012 q = 1) (hb : d337982 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d337012, d337982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337012, d337982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d337013 q = 1) (hb : d337983 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d337013, d337983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337013, d337983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92083 q ha hb
  have h8 (q : Pattern) (ha : d336819 q = 1) (hb : d337797 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336819, d337797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92083 q ha hb
    | true =>
      simp only [d336819, d337797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d337014 q = 1) (hb : d337984 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d337014, d337984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d337014, d337984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336820 q = 1) (hb : d337798 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336820, d337798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d336820, d337798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d337015 q = 1) (hb : d337985 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d337015, d337985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d337015, d337985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d337016 q = 1) (hb : d337986 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d337016, d337986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d337016, d337986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d337017 q = 1) (hb : d337987 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d337017, d337987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d337017, d337987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d336994 q = 1) (hb : d337964 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336994, d337964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336994, d337964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92080 q ha hb
  have h15 (q : Pattern) (ha : d336804 q = 1) (hb : d337783 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336804, d337783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92080 q ha hb
    | true =>
      simp only [d336804, d337783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d336995 q = 1) (hb : d337965 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336995, d337965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d336995, d337965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d336805 q = 1) (hb : d337784 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336805, d337784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d336805, d337784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d336996 q = 1) (hb : d337966 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d336996, d337966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d336996, d337966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d336997 q = 1) (hb : d337967 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d336997, d337967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d336997, d337967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d337003 q = 1) (hb : d337973 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d337003, d337973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d337003, d337973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d337018 q = 1) (hb : d337988 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d337018, d337988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d337018, d337988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro92123 (p : Pattern) (ha : d337028 p = 1) (hb : d337993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337013 q = 1) (hb : d337983 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d337013, d337983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337013, d337983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92083 q ha hb
  have h2 (q : Pattern) (ha : d336819 q = 1) (hb : d337797 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336819, d337797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92083 q ha hb
    | true =>
      simp only [d336819, d337797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d337014 q = 1) (hb : d337984 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d337014, d337984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337014, d337984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336820 q = 1) (hb : d337798 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336820, d337798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336820, d337798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337015 q = 1) (hb : d337985 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d337015, d337985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337015, d337985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d337016 q = 1) (hb : d337986 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d337016, d337986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337016, d337986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d337022 q = 1) (hb : d337992 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d337022, d337992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d337022, d337992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d2361 q = 1) (hb : d337023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2361, d337023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2361, d337023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92085 q ha hb
  have h9 (q : Pattern) (ha : d2080 q = 1) (hb : d336831 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2080, d336831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92085 q ha hb
    | true =>
      simp only [d2080, d336831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2362 q = 1) (hb : d337024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2362, d337024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2362, d337024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2081 q = 1) (hb : d336832 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2081, d336832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2081, d336832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2363 q = 1) (hb : d337025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2363, d337025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2363, d337025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2364 q = 1) (hb : d337026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2364, d337026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2364, d337026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d2365 q = 1) (hb : d337027 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2365, d337027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2365, d337027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d337028 q = 1) (hb : d337993 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d337028, d337993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d337028, d337993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro92124 (p : Pattern) (ha : d337034 p = 1) (hb : d337999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337000 q = 1) (hb : d337970 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d337000, d337970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337000, d337970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92120 q ha hb
  have h2 (q : Pattern) (ha : d337001 q = 1) (hb : d337971 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d337001, d337971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337001, d337971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d337002 q = 1) (hb : d337972 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d337002, d337972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337002, d337972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d337005 q = 1) (hb : d337975 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d337005, d337975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92120 q ha hb
    | true =>
      simp only [d337005, d337975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92121 q ha hb
  have h5 (q : Pattern) (ha : d337006 q = 1) (hb : d337976 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d337006, d337976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337006, d337976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d337007 q = 1) (hb : d337977 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d337007, d337977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337007, d337977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d337008 q = 1) (hb : d337978 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d337008, d337978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337008, d337978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d337019 q = 1) (hb : d337989 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d337019, d337989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92120 q ha hb
    | true =>
      simp only [d337019, d337989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92122 q ha hb
  have h9 (q : Pattern) (ha : d337020 q = 1) (hb : d337990 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d337020, d337990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337020, d337990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d337021 q = 1) (hb : d337991 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d337021, d337991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337021, d337991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d337029 q = 1) (hb : d337994 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d337029, d337994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92122 q ha hb
    | true =>
      simp only [d337029, d337994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92123 q ha hb
  have h12 (q : Pattern) (ha : d337030 q = 1) (hb : d337995 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d337030, d337995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337030, d337995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d337031 q = 1) (hb : d337996 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d337031, d337996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337031, d337996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d337032 q = 1) (hb : d337997 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d337032, d337997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d337032, d337997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d337033 q = 1) (hb : d337998 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d337033, d337998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d337033, d337998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d337034 q = 1) (hb : d337999 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d337034, d337999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d337034, d337999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro92125 (p : Pattern) (ha : d337039 p = 1) (hb : d338004 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337019 q = 1) (hb : d337989 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d337019, d337989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92120 q ha hb
    | true =>
      simp only [d337019, d337989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92122 q ha hb
  have h2 (q : Pattern) (ha : d337020 q = 1) (hb : d337990 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d337020, d337990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337020, d337990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d337021 q = 1) (hb : d337991 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d337021, d337991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337021, d337991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d337029 q = 1) (hb : d337994 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d337029, d337994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92122 q ha hb
    | true =>
      simp only [d337029, d337994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92123 q ha hb
  have h5 (q : Pattern) (ha : d337030 q = 1) (hb : d337995 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d337030, d337995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337030, d337995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d337031 q = 1) (hb : d337996 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d337031, d337996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337031, d337996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d337032 q = 1) (hb : d337997 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d337032, d337997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337032, d337997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d337037 q = 1) (hb : d338002 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d337037, d338002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d337037, d338002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d337038 q = 1) (hb : d338003 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d337038, d338003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d337038, d338003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d337039 q = 1) (hb : d338004 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d337039, d338004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d337039, d338004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro92126 (p : Pattern) (ha : d337045 p = 1) (hb : d338010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337035 q = 1) (hb : d338000 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d337035, d338000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92124 q ha hb
    | true =>
      simp only [d337035, d338000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d337036 q = 1) (hb : d338001 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d337036, d338001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337036, d338001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d337040 q = 1) (hb : d338005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d337040, d338005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92125 q ha hb
    | true =>
      simp only [d337040, d338005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d337041 q = 1) (hb : d338006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d337041, d338006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337041, d338006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d337042 q = 1) (hb : d338007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d337042, d338007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337042, d338007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d337043 q = 1) (hb : d338008 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d337043, d338008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337043, d338008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d337044 q = 1) (hb : d338009 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d337044, d338009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d337044, d338009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d337045 q = 1) (hb : d338010 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d337045, d338010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d337045, d338010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro92127 (p : Pattern) (ha : d337047 p = 1) (hb : d338012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337029 q = 1) (hb : d337994 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d337029, d337994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92122 q ha hb
    | true =>
      simp only [d337029, d337994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92123 q ha hb
  have h2 (q : Pattern) (ha : d337030 q = 1) (hb : d337995 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d337030, d337995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337030, d337995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d337031 q = 1) (hb : d337996 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d337031, d337996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337031, d337996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d337037 q = 1) (hb : d338002 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d337037, d338002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337037, d338002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337046 q = 1) (hb : d338011 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d337046, d338011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337046, d338011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d337047 q = 1) (hb : d338012 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d337047, d338012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337047, d338012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92128 (p : Pattern) (ha : d337053 p = 1) (hb : d338018 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337040 q = 1) (hb : d338005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d337040, d338005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92125 q ha hb
    | true =>
      simp only [d337040, d338005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d337041 q = 1) (hb : d338006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d337041, d338006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337041, d338006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d337048 q = 1) (hb : d338013 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d337048, d338013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92127 q ha hb
    | true =>
      simp only [d337048, d338013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d337049 q = 1) (hb : d338014 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d337049, d338014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337049, d338014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d337050 q = 1) (hb : d338015 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d337050, d338015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337050, d338015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d337051 q = 1) (hb : d338016 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d337051, d338016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337051, d338016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d337052 q = 1) (hb : d338017 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d337052, d338017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d337052, d338017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d337053 q = 1) (hb : d338018 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d337053, d338018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d337053, d338018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro92129 (p : Pattern) (ha : d337066 p = 1) (hb : d338026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337009 q = 1) (hb : d337979 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d337009, d337979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337009, d337979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92082 q ha hb
  have h2 (q : Pattern) (ha : d336814 q = 1) (hb : d337792 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336814, d337792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92082 q ha hb
    | true =>
      simp only [d336814, d337792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d337010 q = 1) (hb : d337980 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d337010, d337980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337010, d337980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336815 q = 1) (hb : d337793 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336815, d337793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336815, d337793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337011 q = 1) (hb : d337981 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d337011, d337981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337011, d337981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d337012 q = 1) (hb : d337982 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d337012, d337982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337012, d337982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d337013 q = 1) (hb : d337983 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d337013, d337983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337013, d337983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92083 q ha hb
  have h8 (q : Pattern) (ha : d336819 q = 1) (hb : d337797 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336819, d337797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92083 q ha hb
    | true =>
      simp only [d336819, d337797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d337014 q = 1) (hb : d337984 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d337014, d337984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d337014, d337984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336820 q = 1) (hb : d337798 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336820, d337798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d336820, d337798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d337015 q = 1) (hb : d337985 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d337015, d337985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d337015, d337985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d337016 q = 1) (hb : d337986 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d337016, d337986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d337016, d337986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d337017 q = 1) (hb : d337987 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d337017, d337987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d337017, d337987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d337061 q = 1) (hb : d338021 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d337061, d338021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337061, d338021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92102 q ha hb
  have h15 (q : Pattern) (ha : d336915 q = 1) (hb : d337885 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336915, d337885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92102 q ha hb
    | true =>
      simp only [d336915, d337885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d337062 q = 1) (hb : d338022 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d337062, d338022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d337062, d338022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d336916 q = 1) (hb : d337886 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336916, d337886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d336916, d337886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d337063 q = 1) (hb : d338023 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d337063, d338023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d337063, d338023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d337064 q = 1) (hb : d338024 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d337064, d338024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d337064, d338024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d337065 q = 1) (hb : d338025 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d337065, d338025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d337065, d338025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d337066 q = 1) (hb : d338026 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d337066, d338026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d337066, d338026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro92130 (p : Pattern) (ha : d337072 p = 1) (hb : d338032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337067 q = 1) (hb : d338027 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d337067, d338027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337067, d338027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92104 q ha hb
  have h2 (q : Pattern) (ha : d336922 q = 1) (hb : d337892 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d336922, d337892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92104 q ha hb
    | true =>
      simp only [d336922, d337892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d337068 q = 1) (hb : d338028 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d337068, d338028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337068, d338028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336923 q = 1) (hb : d337893 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d336923, d337893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336923, d337893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337069 q = 1) (hb : d338029 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d337069, d338029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337069, d338029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d337070 q = 1) (hb : d338030 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d337070, d338030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337070, d338030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d337071 q = 1) (hb : d338031 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d337071, d338031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d337071, d338031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d337072 q = 1) (hb : d338032 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d337072, d338032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d337072, d338032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro92131 (p : Pattern) (ha : d337078 p = 1) (hb : d338038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337019 q = 1) (hb : d337989 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d337019, d337989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92120 q ha hb
    | true =>
      simp only [d337019, d337989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92122 q ha hb
  have h2 (q : Pattern) (ha : d337020 q = 1) (hb : d337990 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d337020, d337990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337020, d337990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d337021 q = 1) (hb : d337991 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d337021, d337991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337021, d337991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d337029 q = 1) (hb : d337994 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d337029, d337994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92122 q ha hb
    | true =>
      simp only [d337029, d337994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92123 q ha hb
  have h5 (q : Pattern) (ha : d337030 q = 1) (hb : d337995 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d337030, d337995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337030, d337995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d337031 q = 1) (hb : d337996 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d337031, d337996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337031, d337996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d337032 q = 1) (hb : d337997 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d337032, d337997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337032, d337997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d337073 q = 1) (hb : d338033 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d337073, d338033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92129 q ha hb
    | true =>
      simp only [d337073, d338033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92130 q ha hb
  have h9 (q : Pattern) (ha : d337074 q = 1) (hb : d338034 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d337074, d338034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337074, d338034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d337075 q = 1) (hb : d338035 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d337075, d338035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337075, d338035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d337076 q = 1) (hb : d338036 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d337076, d338036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d337076, d338036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d337077 q = 1) (hb : d338037 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d337077, d338037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d337077, d338037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d337078 q = 1) (hb : d338038 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d337078, d338038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d337078, d338038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro92132 (p : Pattern) (ha : d337084 p = 1) (hb : d338044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337079 q = 1) (hb : d338039 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d337079, d338039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92131 q ha hb
    | true =>
      simp only [d337079, d338039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d337080 q = 1) (hb : d338040 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d337080, d338040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337080, d338040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d337081 q = 1) (hb : d338041 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d337081, d338041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337081, d338041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d337082 q = 1) (hb : d338042 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d337082, d338042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337082, d338042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337083 q = 1) (hb : d338043 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d337083, d338043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337083, d338043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d337084 q = 1) (hb : d338044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d337084, d338044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337084, d338044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92133 (p : Pattern) (ha : d337090 p = 1) (hb : d338050 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337054 q = 1) (hb : d338019 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337054, d338019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92126 q ha hb
    | true =>
      simp only [d337054, d338019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92128 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d337059 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d337060 q = 1) (hb : d338020 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d337060, d338020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337060, d338020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d337085 q = 1) (hb : d338045 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337085, d338045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92132 q ha hb
    | true =>
      simp only [d337085, d338045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337086 q = 1) (hb : d338046 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d337086, d338046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337086, d338046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d337087 q = 1) (hb : d338047 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d337087, d338047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337087, d338047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d337088 q = 1) (hb : d338048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d337088, d338048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337088, d338048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d337089 q = 1) (hb : d338049 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d337089, d338049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337089, d338049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d337090 q = 1) (hb : d338050 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d337090, d338050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337090, d338050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro92134 (p : Pattern) (ha : d337058 p = 1) (hb : d338055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337048 q = 1) (hb : d338013 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d337048, d338013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92127 q ha hb
    | true =>
      simp only [d337048, d338013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d337049 q = 1) (hb : d338014 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d337049, d338014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337049, d338014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d337055 q = 1) (hb : d338052 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d337055, d338052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337055, d338052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d337056 q = 1) (hb : d338053 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d337056, d338053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337056, d338053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337057 q = 1) (hb : d338054 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d337057, d338054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337057, d338054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d337058 q = 1) (hb : d338055 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d337058, d338055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337058, d338055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92135 (p : Pattern) (ha : d337097 p = 1) (hb : d338061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337092 q = 1) (hb : d338056 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337092, d338056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92134 q ha hb
    | true =>
      simp only [d337092, d338056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d337093 q = 1) (hb : d338057 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d337093, d338057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337093, d338057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d337094 q = 1) (hb : d338058 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d337094, d338058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337094, d338058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d337095 q = 1) (hb : d338059 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d337095, d338059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337095, d338059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d337096 q = 1) (hb : d338060 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d337096, d338060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337096, d338060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d337097 q = 1) (hb : d338061 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d337097, d338061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337097, d338061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92136 (p : Pattern) (ha : d337103 p = 1) (hb : d338067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336864 q = 1) (hb : d337836 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336864, d337836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336864, d337836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92091 q ha hb
  have h2 (q : Pattern) (ha : d336865 q = 1) (hb : d337837 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336865, d337837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336865, d337837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d336874 q = 1) (hb : d337846 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336874, d337846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92091 q ha hb
    | true =>
      simp only [d336874, d337846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92094 q ha hb
  have h4 (q : Pattern) (ha : d336875 q = 1) (hb : d337847 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336875, d337847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336875, d337847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d336876 q = 1) (hb : d337848 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d336876, d337848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d336876, d337848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336967 q = 1) (hb : d337937 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336967, d337937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92108 q ha hb
    | true =>
      simp only [d336967, d337937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92115 q ha hb
  have h7 (q : Pattern) (ha : d336980 q = 1) (hb : d337950 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336980, d337950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92116 q ha hb
    | true =>
      simp only [d336980, d337950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92117 q ha hb
  have h8 (q : Pattern) (ha : d336981 q = 1) (hb : d337951 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336981, d337951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336981, d337951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d336982 q = 1) (hb : d337952 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d336982, d337952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d336982, d337952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d336983 q = 1) (hb : d337953 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d336983, d337953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336983, d337953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d336987 q = 1) (hb : d337957 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336987, d337957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336987, d337957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92118 q ha hb
  have h12 (q : Pattern) (ha : d336989 q = 1) (hb : d337959 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336989, d337959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336989, d337959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92119 q ha hb
  have h13 (q : Pattern) (ha : d336990 q = 1) (hb : d337960 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336990, d337960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d336990, d337960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d336991 q = 1) (hb : d337961 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d336991, d337961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d336991, d337961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d336992 q = 1) (hb : d337962 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d336992, d337962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d336992, d337962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d336993 q = 1) (hb : d337963 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d336993, d337963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336993, d337963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d337091 q = 1) (hb : d338051 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d337091, d338051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337091, d338051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92133 q ha hb
  have h18 (q : Pattern) (ha : d337098 q = 1) (hb : d338062 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d337098, d338062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337098, d338062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92135 q ha hb
  have h19 (q : Pattern) (ha : d337099 q = 1) (hb : d338063 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d337099, d338063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d337099, d338063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d337100 q = 1) (hb : d338064 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d337100, d338064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d337100, d338064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d337101 q = 1) (hb : d338065 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d337101, d338065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d337101, d338065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d337102 q = 1) (hb : d338066 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d337102, d338066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d337102, d338066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d337103 q = 1) (hb : d338067 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d337103, d338067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d337103, d338067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro92137 (p : Pattern) (ha : d337109 p = 1) (hb : d338073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337104 q = 1) (hb : d338068 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d337104, d338068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337104, d338068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92136 q ha hb
  have h2 (q : Pattern) (ha : d337105 q = 1) (hb : d338069 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d337105, d338069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337105, d338069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d337106 q = 1) (hb : d338070 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d337106, d338070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337106, d338070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d337107 q = 1) (hb : d338071 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d337107, d338071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337107, d338071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d337108 q = 1) (hb : d338072 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d337108, d338072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337108, d338072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d337109 q = 1) (hb : d338073 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d337109, d338073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337109, d338073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92138 (p : Pattern) (ha : d337115 p = 1) (hb : d338079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d336180 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d336456 q = 1) (hb : d337454 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d336456, d337454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336456, d337454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92018 q ha hb
  have h3 (q : Pattern) (ha : d336457 q = 1) (hb : d337455 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d336457, d337455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336457, d337455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336458 q = 1) (hb : d337456 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d336458, d337456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336458, d337456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336796 q = 1) (hb : d337778 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d336796, d337778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336796, d337778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92079 q ha hb
  have h6 (q : Pattern) (ha : d336797 q = 1) (hb : d337779 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d336797, d337779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336797, d337779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336798 q = 1) (hb : d337780 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d336798, d337780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336798, d337780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336799 q = 1) (hb : d337781 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d336799, d337781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336799, d337781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d337110 q = 1) (hb : d338074 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d337110, d338074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d337110, d338074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92137 q ha hb
  have h10 (q : Pattern) (ha : d337111 q = 1) (hb : d338075 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d337111, d338075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d337111, d338075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d337112 q = 1) (hb : d338076 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d337112, d338076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d337112, d338076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d337113 q = 1) (hb : d338077 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d337113, d338077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d337113, d338077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d337114 q = 1) (hb : d338078 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d337114, d338078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d337114, d338078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d337115 q = 1) (hb : d338079 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d337115, d338079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d337115, d338079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h14 p ha hb
theorem andIntro92139 (p : Pattern) (ha : d337121 p = 1) (hb : d338085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337116 q = 1) (hb : d338080 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d337116, d338080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92138 q ha hb
    | true =>
      simp only [d337116, d338080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d337117 q = 1) (hb : d338081 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d337117, d338081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337117, d338081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d337118 q = 1) (hb : d338082 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d337118, d338082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337118, d338082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d337119 q = 1) (hb : d338083 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d337119, d338083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337119, d338083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337120 q = 1) (hb : d338084 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d337120, d338084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337120, d338084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d337121 q = 1) (hb : d338085 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d337121, d338085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337121, d338085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92140 (p : Pattern) (ha : d337127 p = 1) (hb : d338091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337122 q = 1) (hb : d338086 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d337122, d338086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92139 q ha hb
    | true =>
      simp only [d337122, d338086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d337123 q = 1) (hb : d338087 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d337123, d338087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337123, d338087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d337124 q = 1) (hb : d338088 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d337124, d338088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337124, d338088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d337125 q = 1) (hb : d338089 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d337125, d338089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337125, d338089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337126 q = 1) (hb : d338090 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d337126, d338090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337126, d338090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d337127 q = 1) (hb : d338091 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d337127, d338091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337127, d338091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92141 (p : Pattern) (ha : d337133 p = 1) (hb : d338097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337128 q = 1) (hb : d338092 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d337128, d338092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92140 q ha hb
    | true =>
      simp only [d337128, d338092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d337129 q = 1) (hb : d338093 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d337129, d338093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337129, d338093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d337130 q = 1) (hb : d338094 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d337130, d338094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337130, d338094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d337131 q = 1) (hb : d338095 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d337131, d338095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337131, d338095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337132 q = 1) (hb : d338096 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d337132, d338096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337132, d338096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d337133 q = 1) (hb : d338097 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d337133, d338097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337133, d338097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92142 (p : Pattern) (ha : d337139 p = 1) (hb : d338103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337134 q = 1) (hb : d338098 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d337134, d338098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92141 q ha hb
    | true =>
      simp only [d337134, d338098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d337135 q = 1) (hb : d338099 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d337135, d338099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337135, d338099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d337136 q = 1) (hb : d338100 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d337136, d338100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337136, d338100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d337137 q = 1) (hb : d338101 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d337137, d338101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337137, d338101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337138 q = 1) (hb : d338102 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d337138, d338102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337138, d338102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d337139 q = 1) (hb : d338103 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d337139, d338103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337139, d338103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92143 (p : Pattern) (ha : d337145 p = 1) (hb : d338109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337140 q = 1) (hb : d338104 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d337140, d338104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92142 q ha hb
    | true =>
      simp only [d337140, d338104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d337141 q = 1) (hb : d338105 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d337141, d338105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337141, d338105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d337142 q = 1) (hb : d338106 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d337142, d338106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337142, d338106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d337143 q = 1) (hb : d338107 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d337143, d338107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337143, d338107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337144 q = 1) (hb : d338108 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d337144, d338108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337144, d338108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d337145 q = 1) (hb : d338109 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d337145, d338109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337145, d338109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92144 (p : Pattern) (ha : d337151 p = 1) (hb : d338115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337146 q = 1) (hb : d338110 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d337146, d338110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92143 q ha hb
    | true =>
      simp only [d337146, d338110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d337147 q = 1) (hb : d338111 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d337147, d338111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337147, d338111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d337148 q = 1) (hb : d338112 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d337148, d338112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337148, d338112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d337149 q = 1) (hb : d338113 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d337149, d338113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337149, d338113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337150 q = 1) (hb : d338114 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d337150, d338114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337150, d338114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d337151 q = 1) (hb : d338115 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d337151, d338115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337151, d338115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92145 (p : Pattern) (ha : d337157 p = 1) (hb : d338121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337152 q = 1) (hb : d338116 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d337152, d338116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92144 q ha hb
    | true =>
      simp only [d337152, d338116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d337153 q = 1) (hb : d338117 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d337153, d338117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337153, d338117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d337154 q = 1) (hb : d338118 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d337154, d338118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337154, d338118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d337155 q = 1) (hb : d338119 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d337155, d338119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337155, d338119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337156 q = 1) (hb : d338120 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d337156, d338120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337156, d338120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d337157 q = 1) (hb : d338121 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d337157, d338121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337157, d338121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92146 (p : Pattern) (ha : d53655 p = 1) (hb : d239126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d204 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91639 q ha hb
    | true =>
      simp only [d204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58400 q ha hb
  have h2 (q : Pattern) (ha : d287 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d289 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53655 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92147 (p : Pattern) (ha : d53665 p = 1) (hb : d239126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91643 q ha hb
    | true =>
      simp only [d244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58405 q ha hb
  have h2 (q : Pattern) (ha : d53661 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53662 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53663 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53664 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53665 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92148 (p : Pattern) (ha : d53671 p = 1) (hb : d239126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91649 q ha hb
    | true =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91650 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92146 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92147 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro92149 (p : Pattern) (ha : d53677 p = 1) (hb : d239126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58723 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53672 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92148 q ha hb
  have h7 (q : Pattern) (ha : d53673 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53674 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53675 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53676 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53677 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro92150 (p : Pattern) (ha : d171078 p = 1) (hb : d239126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16052 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91684 q ha hb
    | true =>
      simp only [d16052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91675 q ha hb
  have h2 (q : Pattern) (ha : d16053 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16054 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16055 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16056 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171078 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92151 (p : Pattern) (ha : d171089 p = 1) (hb : d239126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171084 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91707 q ha hb
    | true =>
      simp only [d171084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91679 q ha hb
  have h2 (q : Pattern) (ha : d171085 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171086 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171087 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171088 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171089 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92152 (p : Pattern) (ha : d171095 p = 1) (hb : d239126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16058 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91683 q ha hb
    | true =>
      simp only [d16058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91685 q ha hb
  have h2 (q : Pattern) (ha : d16059 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171076 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171077 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171079 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92150 q ha hb
  have h6 (q : Pattern) (ha : d171080 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171081 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171082 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d171083 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171090 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92151 q ha hb
  have h11 (q : Pattern) (ha : d171091 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171092 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d171093 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d171094 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d171095 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro92153 (p : Pattern) (ha : d171101 p = 1) (hb : d239126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171096 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92152 q ha hb
  have h2 (q : Pattern) (ha : d171097 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171098 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171099 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171100 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171101 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92154 (p : Pattern) (ha : d239126 p = 1) (hb : d279792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28858 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91732 q ha hb
    | true =>
      simp only [d28858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91720 q ha hb
  have h2 (q : Pattern) (ha : d28859 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28860 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28861 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28862 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d239126 q = 1) (hb : d279792 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d279792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro92155 (p : Pattern) (ha : d239126 p = 1) (hb : d279803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239126 q = 1) (hb : d279798 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d279798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91761 q hb ha
    | true =>
      simp only [d279798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91726 q hb ha
  have h2 (q : Pattern) (ha : d239126 q = 1) (hb : d279799 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d279799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d239126 q = 1) (hb : d279800 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d279800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d239126 q = 1) (hb : d279801 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d279801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d239126 q = 1) (hb : d279802 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d279802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d239126 q = 1) (hb : d279803 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d279803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92156 (p : Pattern) (ha : d239126 p = 1) (hb : d279809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28864 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91731 q ha hb
    | true =>
      simp only [d28864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91733 q ha hb
  have h2 (q : Pattern) (ha : d28865 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d28865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d239126 q = 1) (hb : d279790 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d279790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d279790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d239126 q = 1) (hb : d279791 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d279791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d239126 q = 1) (hb : d279793 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d279793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92154 q ha hb
  have h6 (q : Pattern) (ha : d239126 q = 1) (hb : d279794 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d279794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d279794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d239126 q = 1) (hb : d279795 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d279795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d279795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d239126 q = 1) (hb : d279796 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d279796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d279796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d239126 q = 1) (hb : d279797 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d279797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d279797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d239126 q = 1) (hb : d279804 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d279804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92155 q ha hb
  have h11 (q : Pattern) (ha : d239126 q = 1) (hb : d279805 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d279805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d279805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d239126 q = 1) (hb : d279806 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d279806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d279806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d239126 q = 1) (hb : d279807 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d279807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d279807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d239126 q = 1) (hb : d279808 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d279808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d279808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d239126 q = 1) (hb : d279809 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d279809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d279809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro92157 (p : Pattern) (ha : d239126 p = 1) (hb : d279815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239126 q = 1) (hb : d279810 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d279810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92156 q ha hb
  have h2 (q : Pattern) (ha : d239126 q = 1) (hb : d279811 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d279811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d239126 q = 1) (hb : d279812 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d279812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d239126 q = 1) (hb : d279813 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d279813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d239126 q = 1) (hb : d279814 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d279814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d239126 q = 1) (hb : d279815 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d279815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92158 (p : Pattern) (ha : d239126 p = 1) (hb : d333343 p = 1) : d338124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38894 q = 1) (hb : d239126 q = 1) : d337235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d38894, d337235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91780 q ha hb
    | true =>
      simp only [d38894, d337235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91781 q ha hb
  have h2 (q : Pattern) (ha : d38895 q = 1) (hb : d239126 q = 1) : d337236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d38895, d337236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38895, d337236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38896 q = 1) (hb : d239126 q = 1) : d337237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d38896, d337237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38896, d337237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38897 q = 1) (hb : d239126 q = 1) : d337238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d38897, d337238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38897, d337238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38898 q = 1) (hb : d239126 q = 1) : d337239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d38898, d337239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38898, d337239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d239126 q = 1) (hb : d333343 q = 1) : d338124 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333343, d338124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333343, d338124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro92159 (p : Pattern) (ha : d239126 p = 1) (hb : d333354 p = 1) : d338135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239126 q = 1) (hb : d333349 q = 1) : d338130 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333349, d338130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91819 q hb ha
    | true =>
      simp only [d333349, d338130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91789 q hb ha
  have h2 (q : Pattern) (ha : d239126 q = 1) (hb : d333350 q = 1) : d338131 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333350, d338131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333350, d338131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d239126 q = 1) (hb : d333351 q = 1) : d338132 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333351, d338132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333351, d338132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d239126 q = 1) (hb : d333352 q = 1) : d338133 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333352, d338133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333352, d338133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d239126 q = 1) (hb : d333353 q = 1) : d338134 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333353, d338134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333353, d338134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d239126 q = 1) (hb : d333354 q = 1) : d338135 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333354, d338135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333354, d338135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92160 (p : Pattern) (ha : d239126 p = 1) (hb : d333360 p = 1) : d338141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38900 q = 1) (hb : d239126 q = 1) : d337241 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d38900, d337241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91779 q ha hb
    | true =>
      simp only [d38900, d337241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91782 q ha hb
  have h2 (q : Pattern) (ha : d38901 q = 1) (hb : d239126 q = 1) : d337242 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d38901, d337242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38901, d337242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d239126 q = 1) (hb : d333341 q = 1) : d338122 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333341, d338122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d333341, d338122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d239126 q = 1) (hb : d333342 q = 1) : d338123 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333342, d338123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333342, d338123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d239126 q = 1) (hb : d333344 q = 1) : d338125 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333344, d338125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333344, d338125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92158 q ha hb
  have h6 (q : Pattern) (ha : d239126 q = 1) (hb : d333345 q = 1) : d338126 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333345, d338126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333345, d338126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d239126 q = 1) (hb : d333346 q = 1) : d338127 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333346, d338127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d333346, d338127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d239126 q = 1) (hb : d333347 q = 1) : d338128 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333347, d338128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d333347, d338128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d239126 q = 1) (hb : d333348 q = 1) : d338129 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333348, d338129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333348, d338129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d239126 q = 1) (hb : d333355 q = 1) : d338136 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333355, d338136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333355, d338136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92159 q ha hb
  have h11 (q : Pattern) (ha : d239126 q = 1) (hb : d333356 q = 1) : d338137 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333356, d338137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d333356, d338137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d239126 q = 1) (hb : d333357 q = 1) : d338138 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333357, d338138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d333357, d338138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d239126 q = 1) (hb : d333358 q = 1) : d338139 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333358, d338139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d333358, d338139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d239126 q = 1) (hb : d333359 q = 1) : d338140 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333359, d338140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d333359, d338140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d239126 q = 1) (hb : d333360 q = 1) : d338141 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d333360, d338141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d333360, d338141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro92161 (p : Pattern) (ha : d239126 p = 1) (hb : d333366 p = 1) : d338147 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239126 q = 1) (hb : d333361 q = 1) : d338142 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d333361, d338142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333361, d338142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92160 q ha hb
  have h2 (q : Pattern) (ha : d239126 q = 1) (hb : d333362 q = 1) : d338143 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d333362, d338143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333362, d338143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d239126 q = 1) (hb : d333363 q = 1) : d338144 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d333363, d338144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333363, d338144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d239126 q = 1) (hb : d333364 q = 1) : d338145 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d333364, d338145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333364, d338145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d239126 q = 1) (hb : d333365 q = 1) : d338146 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d333365, d338146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333365, d338146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d239126 q = 1) (hb : d333366 q = 1) : d338147 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d333366, d338147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333366, d338147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92162 (p : Pattern) (ha : d239126 p = 1) (hb : d333372 p = 1) : d338153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39327 q = 1) (hb : d239126 q = 1) : d337535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39327, d337535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91841 q ha hb
    | true =>
      simp only [d39327, d337535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91842 q ha hb
  have h2 (q : Pattern) (ha : d39328 q = 1) (hb : d239126 q = 1) : d337536 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39328, d337536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39328, d337536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39329 q = 1) (hb : d239126 q = 1) : d337537 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39329, d337537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39329, d337537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39330 q = 1) (hb : d239126 q = 1) : d337538 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39330, d337538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39330, d337538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39331 q = 1) (hb : d239126 q = 1) : d337539 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39331, d337539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39331, d337539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d239126 q = 1) (hb : d333372 q = 1) : d338153 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333372, d338153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333372, d338153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro92163 (p : Pattern) (ha : d239126 p = 1) (hb : d333383 p = 1) : d338164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239126 q = 1) (hb : d333378 q = 1) : d338159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333378, d338159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91883 q hb ha
    | true =>
      simp only [d333378, d338159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91850 q hb ha
  have h2 (q : Pattern) (ha : d239126 q = 1) (hb : d333379 q = 1) : d338160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333379, d338160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333379, d338160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d239126 q = 1) (hb : d333380 q = 1) : d338161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333380, d338161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333380, d338161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d239126 q = 1) (hb : d333381 q = 1) : d338162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333381, d338162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333381, d338162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d239126 q = 1) (hb : d333382 q = 1) : d338163 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333382, d338163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333382, d338163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d239126 q = 1) (hb : d333383 q = 1) : d338164 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333383, d338164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333383, d338164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92164 (p : Pattern) (ha : d239126 p = 1) (hb : d333389 p = 1) : d338170 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39333 q = 1) (hb : d239126 q = 1) : d337541 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d39333, d337541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91840 q ha hb
    | true =>
      simp only [d39333, d337541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91843 q ha hb
  have h2 (q : Pattern) (ha : d39334 q = 1) (hb : d239126 q = 1) : d337542 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d39334, d337542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39334, d337542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d239126 q = 1) (hb : d333370 q = 1) : d338151 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333370, d338151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d333370, d338151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d239126 q = 1) (hb : d333371 q = 1) : d338152 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333371, d338152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333371, d338152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d239126 q = 1) (hb : d333373 q = 1) : d338154 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333373, d338154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333373, d338154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92162 q ha hb
  have h6 (q : Pattern) (ha : d239126 q = 1) (hb : d333374 q = 1) : d338155 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333374, d338155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333374, d338155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d239126 q = 1) (hb : d333375 q = 1) : d338156 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333375, d338156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d333375, d338156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d239126 q = 1) (hb : d333376 q = 1) : d338157 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333376, d338157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d333376, d338157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d239126 q = 1) (hb : d333377 q = 1) : d338158 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333377, d338158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333377, d338158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d239126 q = 1) (hb : d333384 q = 1) : d338165 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333384, d338165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333384, d338165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92163 q ha hb
  have h11 (q : Pattern) (ha : d239126 q = 1) (hb : d333385 q = 1) : d338166 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333385, d338166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d333385, d338166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d239126 q = 1) (hb : d333386 q = 1) : d338167 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333386, d338167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d333386, d338167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d239126 q = 1) (hb : d333387 q = 1) : d338168 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333387, d338168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d333387, d338168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d239126 q = 1) (hb : d333388 q = 1) : d338169 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333388, d338169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d333388, d338169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d239126 q = 1) (hb : d333389 q = 1) : d338170 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d333389, d338170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d333389, d338170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro92165 (p : Pattern) (ha : d239126 p = 1) (hb : d333395 p = 1) : d338176 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239126 q = 1) (hb : d333390 q = 1) : d338171 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d333390, d338171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333390, d338171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92164 q ha hb
  have h2 (q : Pattern) (ha : d239126 q = 1) (hb : d333391 q = 1) : d338172 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d333391, d338172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333391, d338172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d239126 q = 1) (hb : d333392 q = 1) : d338173 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d333392, d338173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333392, d338173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d239126 q = 1) (hb : d333393 q = 1) : d338174 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d333393, d338174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333393, d338174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d239126 q = 1) (hb : d333394 q = 1) : d338175 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d333394, d338175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333394, d338175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d239126 q = 1) (hb : d333395 q = 1) : d338176 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d333395, d338176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333395, d338176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92166 (p : Pattern) (ha : d239126 p = 1) (hb : d333402 p = 1) : d338183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39765 q = 1) (hb : d239126 q = 1) : d337840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39765, d337840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91905 q ha hb
    | true =>
      simp only [d39765, d337840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91906 q ha hb
  have h2 (q : Pattern) (ha : d39766 q = 1) (hb : d239126 q = 1) : d337841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39766, d337841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39766, d337841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39767 q = 1) (hb : d239126 q = 1) : d337842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39767, d337842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39767, d337842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39768 q = 1) (hb : d239126 q = 1) : d337843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39768, d337843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39768, d337843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39769 q = 1) (hb : d239126 q = 1) : d337844 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39769, d337844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39769, d337844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d239126 q = 1) (hb : d333402 q = 1) : d338183 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333402, d338183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333402, d338183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro92167 (p : Pattern) (ha : d239126 p = 1) (hb : d333413 p = 1) : d338194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239126 q = 1) (hb : d333408 q = 1) : d338189 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333408, d338189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91946 q hb ha
    | true =>
      simp only [d333408, d338189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91914 q hb ha
  have h2 (q : Pattern) (ha : d239126 q = 1) (hb : d333409 q = 1) : d338190 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333409, d338190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333409, d338190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d239126 q = 1) (hb : d333410 q = 1) : d338191 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333410, d338191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333410, d338191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d239126 q = 1) (hb : d333411 q = 1) : d338192 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333411, d338192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333411, d338192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d239126 q = 1) (hb : d333412 q = 1) : d338193 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333412, d338193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333412, d338193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d239126 q = 1) (hb : d333413 q = 1) : d338194 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333413, d338194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333413, d338194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92168 (p : Pattern) (ha : d239126 p = 1) (hb : d333419 p = 1) : d338200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39771 q = 1) (hb : d239126 q = 1) : d337846 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d39771, d337846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91904 q ha hb
    | true =>
      simp only [d39771, d337846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91907 q ha hb
  have h2 (q : Pattern) (ha : d39772 q = 1) (hb : d239126 q = 1) : d337847 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d39772, d337847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39772, d337847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d239126 q = 1) (hb : d333400 q = 1) : d338181 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333400, d338181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d333400, d338181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d239126 q = 1) (hb : d333401 q = 1) : d338182 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333401, d338182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333401, d338182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d239126 q = 1) (hb : d333403 q = 1) : d338184 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333403, d338184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333403, d338184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92166 q ha hb
  have h6 (q : Pattern) (ha : d239126 q = 1) (hb : d333404 q = 1) : d338185 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333404, d338185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333404, d338185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d239126 q = 1) (hb : d333405 q = 1) : d338186 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333405, d338186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d333405, d338186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d239126 q = 1) (hb : d333406 q = 1) : d338187 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333406, d338187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d333406, d338187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d239126 q = 1) (hb : d333407 q = 1) : d338188 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333407, d338188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333407, d338188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d239126 q = 1) (hb : d333414 q = 1) : d338195 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333414, d338195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333414, d338195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92167 q ha hb
  have h11 (q : Pattern) (ha : d239126 q = 1) (hb : d333415 q = 1) : d338196 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333415, d338196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d333415, d338196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d239126 q = 1) (hb : d333416 q = 1) : d338197 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333416, d338197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d333416, d338197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d239126 q = 1) (hb : d333417 q = 1) : d338198 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333417, d338198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d333417, d338198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d239126 q = 1) (hb : d333418 q = 1) : d338199 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333418, d338199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d333418, d338199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d239126 q = 1) (hb : d333419 q = 1) : d338200 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d333419, d338200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d333419, d338200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro92169 (p : Pattern) (ha : d239126 p = 1) (hb : d333425 p = 1) : d338206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239126 q = 1) (hb : d333420 q = 1) : d338201 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d333420, d338201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333420, d338201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92168 q ha hb
  have h2 (q : Pattern) (ha : d239126 q = 1) (hb : d333421 q = 1) : d338202 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d333421, d338202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333421, d338202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d239126 q = 1) (hb : d333422 q = 1) : d338203 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d333422, d338203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333422, d338203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d239126 q = 1) (hb : d333423 q = 1) : d338204 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d333423, d338204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333423, d338204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d239126 q = 1) (hb : d333424 q = 1) : d338205 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d333424, d338205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333424, d338205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d239126 q = 1) (hb : d333425 q = 1) : d338206 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d333425, d338206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333425, d338206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92170 (p : Pattern) (ha : d239126 p = 1) (hb : d333431 p = 1) : d338212 p = 1 := by
  have h0 (q : Pattern) (ha : d171102 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92149 q ha hb
    | true =>
      simp only [d171102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92153 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d239126 q = 1) (hb : d279816 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d279816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d279816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92157 q ha hb
  have h3 (q : Pattern) (ha : d239126 q = 1) (hb : d279817 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d279817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d279817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d239126 q = 1) (hb : d333367 q = 1) : d338148 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d333367, d338148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333367, d338148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92161 q ha hb
  have h5 (q : Pattern) (ha : d239126 q = 1) (hb : d333368 q = 1) : d338149 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d333368, d338149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333368, d338149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d239126 q = 1) (hb : d333369 q = 1) : d338150 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d333369, d338150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333369, d338150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d239126 q = 1) (hb : d333396 q = 1) : d338177 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d333396, d338177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333396, d338177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92165 q ha hb
  have h8 (q : Pattern) (ha : d239126 q = 1) (hb : d333397 q = 1) : d338178 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d333397, d338178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333397, d338178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d239126 q = 1) (hb : d333398 q = 1) : d338179 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d333398, d338179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333398, d338179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d239126 q = 1) (hb : d333399 q = 1) : d338180 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d333399, d338180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d333399, d338180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d239126 q = 1) (hb : d333426 q = 1) : d338207 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d333426, d338207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333426, d338207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92169 q ha hb
  have h12 (q : Pattern) (ha : d239126 q = 1) (hb : d333427 q = 1) : d338208 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d333427, d338208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333427, d338208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d239126 q = 1) (hb : d333428 q = 1) : d338209 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d333428, d338209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333428, d338209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d239126 q = 1) (hb : d333429 q = 1) : d338210 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d333429, d338210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333429, d338210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d239126 q = 1) (hb : d333430 q = 1) : d338211 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d333430, d338211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d333430, d338211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d239126 q = 1) (hb : d333431 q = 1) : d338212 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d333431, d338212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d333431, d338212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro92171 (p : Pattern) (ha : d239126 p = 1) (hb : d333437 p = 1) : d338218 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239126 q = 1) (hb : d333432 q = 1) : d338213 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d333432, d338213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92170 q ha hb
    | true =>
      simp only [d333432, d338213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d239126 q = 1) (hb : d333433 q = 1) : d338214 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d333433, d338214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d333433, d338214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d239126 q = 1) (hb : d333434 q = 1) : d338215 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d333434, d338215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333434, d338215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d239126 q = 1) (hb : d333435 q = 1) : d338216 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d333435, d338216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333435, d338216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d239126 q = 1) (hb : d333436 q = 1) : d338217 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d333436, d338217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333436, d338217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d239126 q = 1) (hb : d333437 q = 1) : d338218 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d333437, d338218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333437, d338218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92172 (p : Pattern) (ha : d239127 p = 1) (hb : d333443 p = 1) : d338224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239126 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239126 q = 1) (hb : d333438 q = 1) : d338219 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d333438, d338219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92171 q ha hb
    | true =>
      simp only [d333438, d338219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d239126 q = 1) (hb : d333439 q = 1) : d338220 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d333439, d338220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d333439, d338220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d239126 q = 1) (hb : d333440 q = 1) : d338221 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d333440, d338221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333440, d338221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d239126 q = 1) (hb : d333441 q = 1) : d338222 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d333441, d338222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333441, d338222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d239126 q = 1) (hb : d333442 q = 1) : d338223 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d333442, d338223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333442, d338223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d239127 q = 1) (hb : d333443 q = 1) : d338224 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d239127, d333443, d338224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239127, d333443, d338224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro92173 (p : Pattern) (ha : d239127 p = 1) (hb : d333449 p = 1) : d338230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239127 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239127 q = 1) (hb : d333444 q = 1) : d338225 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d333444, d338225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92172 q ha hb
    | true =>
      simp only [d333444, d338225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d239127 q = 1) (hb : d333445 q = 1) : d338226 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d333445, d338226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d333445, d338226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d239127 q = 1) (hb : d333446 q = 1) : d338227 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d333446, d338227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333446, d338227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d239127 q = 1) (hb : d333447 q = 1) : d338228 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d333447, d338228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333447, d338228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d239127 q = 1) (hb : d333448 q = 1) : d338229 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d333448, d338229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333448, d338229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d239127 q = 1) (hb : d333449 q = 1) : d338230 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d333449, d338230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333449, d338230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92174 (p : Pattern) (ha : d239127 p = 1) (hb : d333455 p = 1) : d338236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239127 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239127 q = 1) (hb : d333450 q = 1) : d338231 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d333450, d338231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92173 q ha hb
    | true =>
      simp only [d333450, d338231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d239127 q = 1) (hb : d333451 q = 1) : d338232 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d333451, d338232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d333451, d338232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d239127 q = 1) (hb : d333452 q = 1) : d338233 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d333452, d338233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333452, d338233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d239127 q = 1) (hb : d333453 q = 1) : d338234 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d333453, d338234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333453, d338234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d239127 q = 1) (hb : d333454 q = 1) : d338235 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d333454, d338235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333454, d338235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d239127 q = 1) (hb : d333455 q = 1) : d338236 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d333455, d338236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333455, d338236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92175 (p : Pattern) (ha : d239127 p = 1) (hb : d333461 p = 1) : d338242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239127 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239127 q = 1) (hb : d333456 q = 1) : d338237 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d333456, d338237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92174 q ha hb
    | true =>
      simp only [d333456, d338237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d239127 q = 1) (hb : d333457 q = 1) : d338238 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d333457, d338238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d333457, d338238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d239127 q = 1) (hb : d333458 q = 1) : d338239 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d333458, d338239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333458, d338239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d239127 q = 1) (hb : d333459 q = 1) : d338240 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d333459, d338240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333459, d338240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d239127 q = 1) (hb : d333460 q = 1) : d338241 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d333460, d338241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333460, d338241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d239127 q = 1) (hb : d333461 q = 1) : d338242 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d333461, d338242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333461, d338242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92176 (p : Pattern) (ha : d239127 p = 1) (hb : d333467 p = 1) : d338248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239127 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239127 q = 1) (hb : d333462 q = 1) : d338243 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d333462, d338243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92175 q ha hb
    | true =>
      simp only [d333462, d338243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d239127 q = 1) (hb : d333463 q = 1) : d338244 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d333463, d338244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d333463, d338244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d239127 q = 1) (hb : d333464 q = 1) : d338245 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d333464, d338245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333464, d338245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d239127 q = 1) (hb : d333465 q = 1) : d338246 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d333465, d338246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333465, d338246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d239127 q = 1) (hb : d333466 q = 1) : d338247 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d333466, d338247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333466, d338247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d239127 q = 1) (hb : d333467 q = 1) : d338248 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d333467, d338248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333467, d338248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92177 (p : Pattern) (ha : d239127 p = 1) (hb : d333473 p = 1) : d338254 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239127 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239127 q = 1) (hb : d333468 q = 1) : d338249 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d333468, d338249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92176 q ha hb
    | true =>
      simp only [d333468, d338249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d239127 q = 1) (hb : d333469 q = 1) : d338250 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d333469, d338250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d333469, d338250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d239127 q = 1) (hb : d333470 q = 1) : d338251 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d333470, d338251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333470, d338251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d239127 q = 1) (hb : d333471 q = 1) : d338252 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d333471, d338252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333471, d338252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d239127 q = 1) (hb : d333472 q = 1) : d338253 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d333472, d338253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333472, d338253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d239127 q = 1) (hb : d333473 q = 1) : d338254 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d333473, d338254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333473, d338254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92178 (p : Pattern) (ha : d336305 p = 1) (hb : d337230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d336245 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d336254 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d336285 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d336219 q = 1) (hb : d337225 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336219, d337225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91974 q ha hb
    | true =>
      simp only [d336219, d337225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91975 q ha hb
  have h5 (q : Pattern) (ha : d336286 q = 1) (hb : d337226 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336286, d337226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d336286, d337226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d336301 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d336302 q = 1) (hb : d337227 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336302, d337227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336302, d337227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d336303 q = 1) (hb : d337228 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336303, d337228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d336303, d337228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d336304 q = 1) (hb : d337229 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336304, d337229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336304, d337229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336305 q = 1) (hb : d337230 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336305, d337230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336305, d337230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro92179 (p : Pattern) (ha : d336326 p = 1) (hb : d337240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d336245 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d336254 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d336285 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d336219 q = 1) (hb : d337225 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336219, d337225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91974 q ha hb
    | true =>
      simp only [d336219, d337225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91975 q ha hb
  have h4 (q : Pattern) (ha : d336286 q = 1) (hb : d337226 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336286, d337226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d336286, d337226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d336301 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d336302 q = 1) (hb : d337227 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336302, d337227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336302, d337227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d336303 q = 1) (hb : d337228 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336303, d337228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336303, d337228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336304 q = 1) (hb : d337229 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336304, d337229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336304, d337229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d336311 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d336316 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d336318 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d336229 q = 1) (hb : d337235 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336229, d337235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91977 q ha hb
    | true =>
      simp only [d336229, d337235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91978 q ha hb
  have h13 (q : Pattern) (ha : d336319 q = 1) (hb : d337236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336319, d337236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d336319, d337236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d336322 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d336323 q = 1) (hb : d337237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336323, d337237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d336323, d337237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d336324 q = 1) (hb : d337238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336324, d337238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d336324, d337238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d336325 q = 1) (hb : d337239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336325, d337239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d336325, d337239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d336326 q = 1) (hb : d337240 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336326, d337240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d336326, d337240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro92180 (p : Pattern) (ha : d336346 p = 1) (hb : d338124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d336318 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d336229 q = 1) (hb : d337235 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336229, d337235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91977 q ha hb
    | true =>
      simp only [d336229, d337235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91978 q ha hb
  have h3 (q : Pattern) (ha : d336319 q = 1) (hb : d337236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336319, d337236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336319, d337236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d336322 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d336323 q = 1) (hb : d337237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336323, d337237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336323, d337237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d336344 q = 1) (hb : d337238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336344, d337238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336344, d337238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336345 q = 1) (hb : d337239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336345, d337239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336345, d337239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336346 q = 1) (hb : d338124 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336346, d338124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336346, d338124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92181 (p : Pattern) (ha : d336436 p = 1) (hb : d338135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d336411 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d336416 q = 1) (hb : d338130 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336416, d338130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92010 q ha hb
    | true =>
      simp only [d336416, d338130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92015 q ha hb
  have h3 (q : Pattern) (ha : d336417 q = 1) (hb : d338131 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336417, d338131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336417, d338131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d336432 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d336433 q = 1) (hb : d338132 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336433, d338132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336433, d338132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d336434 q = 1) (hb : d338133 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336434, d338133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336434, d338133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336435 q = 1) (hb : d338134 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336435, d338134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336435, d338134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336436 q = 1) (hb : d338135 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336436, d338135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336436, d338135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92182 (p : Pattern) (ha : d336449 p = 1) (hb : d338141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d336237 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336327 q = 1) (hb : d337241 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336327, d337241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92178 q ha hb
    | true =>
      simp only [d336327, d337241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92179 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d336340 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d336341 q = 1) (hb : d337242 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336341, d337242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336341, d337242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d336342 q = 1) (hb : d338122 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d336342, d338122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336342, d338122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d336343 q = 1) (hb : d338123 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d336343, d338123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336343, d338123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336347 q = 1) (hb : d338125 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336347, d338125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d336347, d338125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92180 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d336349 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d336350 q = 1) (hb : d338126 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336350, d338126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336350, d338126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d336351 q = 1) (hb : d338127 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d336351, d338127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d336351, d338127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d336352 q = 1) (hb : d338128 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d336352, d338128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336352, d338128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d336353 q = 1) (hb : d338129 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d336353, d338129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336353, d338129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d336437 q = 1) (hb : d338136 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336437, d338136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d336437, d338136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92181 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d336444 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d336445 q = 1) (hb : d338137 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336445, d338137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d336445, d338137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d336446 q = 1) (hb : d338138 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d336446, d338138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d336446, d338138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d336447 q = 1) (hb : d338139 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d336447, d338139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d336447, d338139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d336448 q = 1) (hb : d338140 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d336448, d338140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d336448, d338140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d336449 q = 1) (hb : d338141 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d336449, d338141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d336449, d338141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro92183 (p : Pattern) (ha : d336455 p = 1) (hb : d338147 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336450 q = 1) (hb : d338142 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d336450, d338142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336450, d338142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92182 q ha hb
  have h2 (q : Pattern) (ha : d336451 q = 1) (hb : d338143 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d336451, d338143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336451, d338143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336452 q = 1) (hb : d338144 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d336452, d338144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336452, d338144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336453 q = 1) (hb : d338145 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d336453, d338145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336453, d338145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336454 q = 1) (hb : d338146 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d336454, d338146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336454, d338146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336455 q = 1) (hb : d338147 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d336455, d338147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336455, d338147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92184 (p : Pattern) (ha : d336622 p = 1) (hb : d337530 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d336561 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d336570 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d336587 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d336535 q = 1) (hb : d337525 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336535, d337525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92031 q ha hb
    | true =>
      simp only [d336535, d337525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92032 q ha hb
  have h5 (q : Pattern) (ha : d336588 q = 1) (hb : d337526 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336588, d337526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d336588, d337526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d336618 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d336619 q = 1) (hb : d337527 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336619, d337527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336619, d337527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d336620 q = 1) (hb : d337528 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336620, d337528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d336620, d337528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d336621 q = 1) (hb : d337529 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336621, d337529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336621, d337529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336622 q = 1) (hb : d337530 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336622, d337530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336622, d337530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro92185 (p : Pattern) (ha : d336643 p = 1) (hb : d337540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d336561 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d336570 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d336587 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d336535 q = 1) (hb : d337525 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336535, d337525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92031 q ha hb
    | true =>
      simp only [d336535, d337525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92032 q ha hb
  have h4 (q : Pattern) (ha : d336588 q = 1) (hb : d337526 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336588, d337526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d336588, d337526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d336618 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d336619 q = 1) (hb : d337527 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336619, d337527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336619, d337527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d336620 q = 1) (hb : d337528 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336620, d337528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336620, d337528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336621 q = 1) (hb : d337529 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336621, d337529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336621, d337529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d336628 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d336633 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d336635 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d336545 q = 1) (hb : d337535 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336545, d337535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92034 q ha hb
    | true =>
      simp only [d336545, d337535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92035 q ha hb
  have h13 (q : Pattern) (ha : d336636 q = 1) (hb : d337536 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336636, d337536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d336636, d337536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d336639 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d336640 q = 1) (hb : d337537 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336640, d337537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d336640, d337537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d336641 q = 1) (hb : d337538 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336641, d337538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d336641, d337538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d336642 q = 1) (hb : d337539 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336642, d337539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d336642, d337539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d336643 q = 1) (hb : d337540 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336643, d337540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d336643, d337540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro92186 (p : Pattern) (ha : d336663 p = 1) (hb : d338153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d336635 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d336545 q = 1) (hb : d337535 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336545, d337535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92034 q ha hb
    | true =>
      simp only [d336545, d337535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92035 q ha hb
  have h3 (q : Pattern) (ha : d336636 q = 1) (hb : d337536 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336636, d337536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336636, d337536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d336639 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d336640 q = 1) (hb : d337537 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336640, d337537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336640, d337537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d336661 q = 1) (hb : d337538 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336661, d337538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336661, d337538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336662 q = 1) (hb : d337539 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336662, d337539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336662, d337539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336663 q = 1) (hb : d338153 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336663, d338153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336663, d338153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92187 (p : Pattern) (ha : d336776 p = 1) (hb : d338164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d336740 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d336745 q = 1) (hb : d338159 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336745, d338159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92070 q ha hb
    | true =>
      simp only [d336745, d338159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92076 q ha hb
  have h3 (q : Pattern) (ha : d336746 q = 1) (hb : d338160 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336746, d338160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336746, d338160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d336772 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d336773 q = 1) (hb : d338161 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336773, d338161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336773, d338161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d336774 q = 1) (hb : d338162 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336774, d338162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336774, d338162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336775 q = 1) (hb : d338163 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336775, d338163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336775, d338163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336776 q = 1) (hb : d338164 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336776, d338164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336776, d338164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92188 (p : Pattern) (ha : d336789 p = 1) (hb : d338170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d336553 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336644 q = 1) (hb : d337541 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336644, d337541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92184 q ha hb
    | true =>
      simp only [d336644, d337541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92185 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d336657 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d336658 q = 1) (hb : d337542 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336658, d337542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336658, d337542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d336659 q = 1) (hb : d338151 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d336659, d338151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336659, d338151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d336660 q = 1) (hb : d338152 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d336660, d338152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336660, d338152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336664 q = 1) (hb : d338154 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336664, d338154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d336664, d338154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92186 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d336666 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d336667 q = 1) (hb : d338155 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336667, d338155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336667, d338155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d336668 q = 1) (hb : d338156 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d336668, d338156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d336668, d338156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d336669 q = 1) (hb : d338157 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d336669, d338157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336669, d338157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d336670 q = 1) (hb : d338158 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d336670, d338158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336670, d338158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d336777 q = 1) (hb : d338165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336777, d338165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d336777, d338165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92187 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d336784 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d336785 q = 1) (hb : d338166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336785, d338166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d336785, d338166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d336786 q = 1) (hb : d338167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d336786, d338167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d336786, d338167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d336787 q = 1) (hb : d338168 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d336787, d338168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d336787, d338168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d336788 q = 1) (hb : d338169 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d336788, d338169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d336788, d338169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d336789 q = 1) (hb : d338170 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d336789, d338170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d336789, d338170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro92189 (p : Pattern) (ha : d336795 p = 1) (hb : d338176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336790 q = 1) (hb : d338171 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d336790, d338171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336790, d338171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92188 q ha hb
  have h2 (q : Pattern) (ha : d336791 q = 1) (hb : d338172 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d336791, d338172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336791, d338172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d336792 q = 1) (hb : d338173 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d336792, d338173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336792, d338173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336793 q = 1) (hb : d338174 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d336793, d338174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336793, d338174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336794 q = 1) (hb : d338175 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d336794, d338175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336794, d338175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d336795 q = 1) (hb : d338176 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d336795, d338176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336795, d338176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92190 (p : Pattern) (ha : d336945 p = 1) (hb : d337835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d336884 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d336893 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d336910 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d336858 q = 1) (hb : d337830 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336858, d337830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92089 q ha hb
    | true =>
      simp only [d336858, d337830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92090 q ha hb
  have h5 (q : Pattern) (ha : d336911 q = 1) (hb : d337831 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336911, d337831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d336911, d337831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d336941 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d336942 q = 1) (hb : d337832 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336942, d337832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d336942, d337832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d336943 q = 1) (hb : d337833 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336943, d337833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d336943, d337833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d336944 q = 1) (hb : d337834 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336944, d337834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336944, d337834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d336945 q = 1) (hb : d337835 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336945, d337835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336945, d337835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro92191 (p : Pattern) (ha : d336966 p = 1) (hb : d337845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d336884 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d336893 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d336910 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d336858 q = 1) (hb : d337830 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336858, d337830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92089 q ha hb
    | true =>
      simp only [d336858, d337830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92090 q ha hb
  have h4 (q : Pattern) (ha : d336911 q = 1) (hb : d337831 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336911, d337831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d336911, d337831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d336941 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d336942 q = 1) (hb : d337832 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336942, d337832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336942, d337832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d336943 q = 1) (hb : d337833 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336943, d337833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336943, d337833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336944 q = 1) (hb : d337834 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336944, d337834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336944, d337834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d336951 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d336956 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d336958 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d336868 q = 1) (hb : d337840 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336868, d337840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92092 q ha hb
    | true =>
      simp only [d336868, d337840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92093 q ha hb
  have h13 (q : Pattern) (ha : d336959 q = 1) (hb : d337841 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336959, d337841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d336959, d337841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d336962 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d336963 q = 1) (hb : d337842 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336963, d337842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d336963, d337842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d336964 q = 1) (hb : d337843 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336964, d337843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d336964, d337843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d336965 q = 1) (hb : d337844 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336965, d337844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d336965, d337844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d336966 q = 1) (hb : d337845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336966, d337845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d336966, d337845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro92192 (p : Pattern) (ha : d336986 p = 1) (hb : d338183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d336958 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d336868 q = 1) (hb : d337840 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d336868, d337840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92092 q ha hb
    | true =>
      simp only [d336868, d337840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92093 q ha hb
  have h3 (q : Pattern) (ha : d336959 q = 1) (hb : d337841 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d336959, d337841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336959, d337841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d336962 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d336963 q = 1) (hb : d337842 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d336963, d337842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336963, d337842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d336984 q = 1) (hb : d337843 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d336984, d337843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336984, d337843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336985 q = 1) (hb : d337844 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d336985, d337844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336985, d337844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336986 q = 1) (hb : d338183 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d336986, d338183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336986, d338183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92193 (p : Pattern) (ha : d337090 p = 1) (hb : d338194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d337054 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d337059 q = 1) (hb : d338189 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337059, d338189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92128 q ha hb
    | true =>
      simp only [d337059, d338189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92134 q ha hb
  have h3 (q : Pattern) (ha : d337060 q = 1) (hb : d338190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d337060, d338190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d337060, d338190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d337086 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d337087 q = 1) (hb : d338191 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d337087, d338191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337087, d338191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d337088 q = 1) (hb : d338192 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d337088, d338192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337088, d338192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d337089 q = 1) (hb : d338193 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d337089, d338193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337089, d338193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d337090 q = 1) (hb : d338194 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d337090, d338194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337090, d338194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92194 (p : Pattern) (ha : d337103 p = 1) (hb : d338200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d336876 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d336967 q = 1) (hb : d337846 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336967, d337846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92190 q ha hb
    | true =>
      simp only [d336967, d337846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92191 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d336980 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d336981 q = 1) (hb : d337847 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336981, d337847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d336981, d337847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d336982 q = 1) (hb : d338181 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d336982, d338181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d336982, d338181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d336983 q = 1) (hb : d338182 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d336983, d338182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336983, d338182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336987 q = 1) (hb : d338184 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d336987, d338184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d336987, d338184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92192 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d336989 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d336990 q = 1) (hb : d338185 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d336990, d338185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d336990, d338185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d336991 q = 1) (hb : d338186 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d336991, d338186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d336991, d338186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d336992 q = 1) (hb : d338187 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d336992, d338187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d336992, d338187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d336993 q = 1) (hb : d338188 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d336993, d338188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d336993, d338188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d337091 q = 1) (hb : d338195 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d337091, d338195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d337091, d338195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92193 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d337098 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d337099 q = 1) (hb : d338196 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d337099, d338196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d337099, d338196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d337100 q = 1) (hb : d338197 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d337100, d338197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d337100, d338197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d337101 q = 1) (hb : d338198 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d337101, d338198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d337101, d338198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d337102 q = 1) (hb : d338199 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d337102, d338199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d337102, d338199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d337103 q = 1) (hb : d338200 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d337103, d338200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d337103, d338200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro92195 (p : Pattern) (ha : d337109 p = 1) (hb : d338206 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337104 q = 1) (hb : d338201 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d337104, d338201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337104, d338201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92194 q ha hb
  have h2 (q : Pattern) (ha : d337105 q = 1) (hb : d338202 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d337105, d338202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337105, d338202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d337106 q = 1) (hb : d338203 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d337106, d338203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337106, d338203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d337107 q = 1) (hb : d338204 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d337107, d338204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337107, d338204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d337108 q = 1) (hb : d338205 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d337108, d338205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337108, d338205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d337109 q = 1) (hb : d338206 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d337109, d338206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d337109, d338206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92196 (p : Pattern) (ha : d337115 p = 1) (hb : d338212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d336180 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d336456 q = 1) (hb : d338148 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d336456, d338148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336456, d338148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92183 q ha hb
  have h3 (q : Pattern) (ha : d336457 q = 1) (hb : d338149 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d336457, d338149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336457, d338149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d336458 q = 1) (hb : d338150 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d336458, d338150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d336458, d338150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d336796 q = 1) (hb : d338177 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d336796, d338177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336796, d338177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92189 q ha hb
  have h6 (q : Pattern) (ha : d336797 q = 1) (hb : d338178 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d336797, d338178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336797, d338178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d336798 q = 1) (hb : d338179 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d336798, d338179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d336798, d338179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d336799 q = 1) (hb : d338180 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d336799, d338180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d336799, d338180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d337110 q = 1) (hb : d338207 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d337110, d338207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d337110, d338207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92195 q ha hb
  have h10 (q : Pattern) (ha : d337111 q = 1) (hb : d338208 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d337111, d338208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d337111, d338208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d337112 q = 1) (hb : d338209 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d337112, d338209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d337112, d338209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d337113 q = 1) (hb : d338210 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d337113, d338210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d337113, d338210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d337114 q = 1) (hb : d338211 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d337114, d338211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d337114, d338211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d337115 q = 1) (hb : d338212 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d337115, d338212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d337115, d338212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h14 p ha hb
theorem andIntro92197 (p : Pattern) (ha : d337121 p = 1) (hb : d338218 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337116 q = 1) (hb : d338213 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d337116, d338213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92196 q ha hb
    | true =>
      simp only [d337116, d338213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d337117 q = 1) (hb : d338214 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d337117, d338214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337117, d338214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d337118 q = 1) (hb : d338215 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d337118, d338215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337118, d338215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d337119 q = 1) (hb : d338216 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d337119, d338216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337119, d338216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337120 q = 1) (hb : d338217 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d337120, d338217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337120, d338217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d337121 q = 1) (hb : d338218 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d337121, d338218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337121, d338218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92198 (p : Pattern) (ha : d337127 p = 1) (hb : d338224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337122 q = 1) (hb : d338219 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d337122, d338219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92197 q ha hb
    | true =>
      simp only [d337122, d338219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d337123 q = 1) (hb : d338220 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d337123, d338220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337123, d338220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d337124 q = 1) (hb : d338221 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d337124, d338221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337124, d338221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d337125 q = 1) (hb : d338222 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d337125, d338222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337125, d338222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337126 q = 1) (hb : d338223 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d337126, d338223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337126, d338223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d337127 q = 1) (hb : d338224 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d337127, d338224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337127, d338224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92199 (p : Pattern) (ha : d337133 p = 1) (hb : d338230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337128 q = 1) (hb : d338225 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d337128, d338225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92198 q ha hb
    | true =>
      simp only [d337128, d338225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d337129 q = 1) (hb : d338226 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d337129, d338226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337129, d338226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d337130 q = 1) (hb : d338227 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d337130, d338227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337130, d338227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d337131 q = 1) (hb : d338228 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d337131, d338228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337131, d338228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337132 q = 1) (hb : d338229 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d337132, d338229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337132, d338229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d337133 q = 1) (hb : d338230 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d337133, d338230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337133, d338230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92200 (p : Pattern) (ha : d337139 p = 1) (hb : d338236 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337134 q = 1) (hb : d338231 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d337134, d338231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92199 q ha hb
    | true =>
      simp only [d337134, d338231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d337135 q = 1) (hb : d338232 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d337135, d338232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337135, d338232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d337136 q = 1) (hb : d338233 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d337136, d338233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337136, d338233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d337137 q = 1) (hb : d338234 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d337137, d338234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337137, d338234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337138 q = 1) (hb : d338235 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d337138, d338235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337138, d338235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d337139 q = 1) (hb : d338236 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d337139, d338236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337139, d338236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92201 (p : Pattern) (ha : d337145 p = 1) (hb : d338242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337140 q = 1) (hb : d338237 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d337140, d338237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92200 q ha hb
    | true =>
      simp only [d337140, d338237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d337141 q = 1) (hb : d338238 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d337141, d338238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337141, d338238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d337142 q = 1) (hb : d338239 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d337142, d338239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337142, d338239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d337143 q = 1) (hb : d338240 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d337143, d338240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337143, d338240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337144 q = 1) (hb : d338241 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d337144, d338241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337144, d338241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d337145 q = 1) (hb : d338242 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d337145, d338242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337145, d338242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92202 (p : Pattern) (ha : d337151 p = 1) (hb : d338248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337146 q = 1) (hb : d338243 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d337146, d338243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92201 q ha hb
    | true =>
      simp only [d337146, d338243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d337147 q = 1) (hb : d338244 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d337147, d338244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337147, d338244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d337148 q = 1) (hb : d338245 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d337148, d338245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337148, d338245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d337149 q = 1) (hb : d338246 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d337149, d338246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337149, d338246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337150 q = 1) (hb : d338247 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d337150, d338247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337150, d338247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d337151 q = 1) (hb : d338248 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d337151, d338248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337151, d338248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92203 (p : Pattern) (ha : d337157 p = 1) (hb : d338254 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337152 q = 1) (hb : d338249 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d337152, d338249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92202 q ha hb
    | true =>
      simp only [d337152, d338249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d337153 q = 1) (hb : d338250 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d337153, d338250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337153, d338250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d337154 q = 1) (hb : d338251 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d337154, d338251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337154, d338251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d337155 q = 1) (hb : d338252 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d337155, d338252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337155, d338252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d337156 q = 1) (hb : d338253 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d337156, d338253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337156, d338253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d337157 q = 1) (hb : d338254 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d337157, d338254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337157, d338254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro92204 (p : Pattern) (ha : d337230 p = 1) (hb : d338379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d334313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d334322 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d334353 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d337225 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d337226 q = 1) (hb : d338375 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d337226, d338375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337226, d338375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d334425 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d337227 q = 1) (hb : d338376 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d337227, d338376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337227, d338376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d337228 q = 1) (hb : d338377 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d337228, d338377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337228, d338377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d337229 q = 1) (hb : d338378 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d337229, d338378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337229, d338378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d337230 q = 1) (hb : d338379 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d337230, d338379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d337230, d338379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro92205 (p : Pattern) (ha : d337240 p = 1) (hb : d338384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d334313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d334322 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d334353 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d337225 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d337226 q = 1) (hb : d338375 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d337226, d338375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337226, d338375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d334425 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d337227 q = 1) (hb : d338376 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d337227, d338376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337227, d338376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d337228 q = 1) (hb : d338377 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d337228, d338377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337228, d338377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d337229 q = 1) (hb : d338378 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d337229, d338378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d337229, d338378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d334435 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d334440 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d334442 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d337235 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d337236 q = 1) (hb : d338380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d337236, d338380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d337236, d338380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d334449 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d337237 q = 1) (hb : d338381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d337237, d338381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d337237, d338381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d337238 q = 1) (hb : d338382 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d337238, d338382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d337238, d338382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d337239 q = 1) (hb : d338383 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d337239, d338383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d337239, d338383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d337240 q = 1) (hb : d338384 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d337240, d338384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d337240, d338384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro92206 (p : Pattern) (ha : d338124 p = 1) (hb : d338391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d334442 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d337235 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d337236 q = 1) (hb : d338380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d337236, d338380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337236, d338380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d334449 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d337237 q = 1) (hb : d338381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d337237, d338381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337237, d338381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d337238 q = 1) (hb : d338389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d337238, d338389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d337238, d338389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d337239 q = 1) (hb : d338390 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d337239, d338390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d337239, d338390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d338124 q = 1) (hb : d338391 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d338124, d338391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338124, d338391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92207 (p : Pattern) (ha : d338135 p = 1) (hb : d338401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d334538 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d338130 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d338131 q = 1) (hb : d338397 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d338131, d338397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338131, d338397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d334599 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d338132 q = 1) (hb : d338398 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d338132, d338398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338132, d338398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d338133 q = 1) (hb : d338399 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d338133, d338399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338133, d338399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d338134 q = 1) (hb : d338400 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d338134, d338400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338134, d338400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d338135 q = 1) (hb : d338401 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d338135, d338401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338135, d338401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92208 (p : Pattern) (ha : d338141 p = 1) (hb : d338407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d334305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337241 q = 1) (hb : d338385 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d337241, d338385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92204 q ha hb
    | true =>
      simp only [d337241, d338385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92205 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d334467 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d337242 q = 1) (hb : d338386 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d337242, d338386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337242, d338386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d338122 q = 1) (hb : d338387 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338122, d338387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338122, d338387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d338123 q = 1) (hb : d338388 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338123, d338388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338123, d338388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d338125 q = 1) (hb : d338392 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d338125, d338392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338125, d338392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92206 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d334476 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d338126 q = 1) (hb : d338393 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d338126, d338393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d338126, d338393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d338127 q = 1) (hb : d338394 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338127, d338394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d338127, d338394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d338128 q = 1) (hb : d338395 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338128, d338395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d338128, d338395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d338129 q = 1) (hb : d338396 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d338129, d338396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d338129, d338396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d338136 q = 1) (hb : d338402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d338136, d338402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338136, d338402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92207 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d334615 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d338137 q = 1) (hb : d338403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d338137, d338403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d338137, d338403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d338138 q = 1) (hb : d338404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338138, d338404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d338138, d338404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d338139 q = 1) (hb : d338405 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338139, d338405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d338139, d338405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d338140 q = 1) (hb : d338406 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d338140, d338406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d338140, d338406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d338141 q = 1) (hb : d338407 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d338141, d338407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d338141, d338407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro92209 (p : Pattern) (ha : d338147 p = 1) (hb : d338413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d338142 q = 1) (hb : d338408 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d338142, d338408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338142, d338408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92208 q ha hb
  have h2 (q : Pattern) (ha : d338143 q = 1) (hb : d338409 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d338143, d338409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338143, d338409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d338144 q = 1) (hb : d338410 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d338144, d338410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338144, d338410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d338145 q = 1) (hb : d338411 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d338145, d338411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338145, d338411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d338146 q = 1) (hb : d338412 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d338146, d338412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338146, d338412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d338147 q = 1) (hb : d338413 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d338147, d338413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338147, d338413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92210 (p : Pattern) (ha : d337530 p = 1) (hb : d338421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d334732 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d334741 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d334758 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d337525 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d337526 q = 1) (hb : d338417 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d337526, d338417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337526, d338417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d334866 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d337527 q = 1) (hb : d338418 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d337527, d338418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337527, d338418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d337528 q = 1) (hb : d338419 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d337528, d338419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337528, d338419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d337529 q = 1) (hb : d338420 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d337529, d338420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337529, d338420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d337530 q = 1) (hb : d338421 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d337530, d338421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d337530, d338421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro92211 (p : Pattern) (ha : d337540 p = 1) (hb : d338426 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d334732 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d334741 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d334758 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d337525 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d337526 q = 1) (hb : d338417 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d337526, d338417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337526, d338417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d334866 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d337527 q = 1) (hb : d338418 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d337527, d338418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337527, d338418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d337528 q = 1) (hb : d338419 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d337528, d338419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337528, d338419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d337529 q = 1) (hb : d338420 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d337529, d338420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d337529, d338420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d334876 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d334881 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d334883 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d337535 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d337536 q = 1) (hb : d338422 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d337536, d338422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d337536, d338422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d334890 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d337537 q = 1) (hb : d338423 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d337537, d338423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d337537, d338423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d337538 q = 1) (hb : d338424 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d337538, d338424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d337538, d338424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d337539 q = 1) (hb : d338425 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d337539, d338425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d337539, d338425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d337540 q = 1) (hb : d338426 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d337540, d338426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d337540, d338426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro92212 (p : Pattern) (ha : d338153 p = 1) (hb : d338433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d334883 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d337535 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d337536 q = 1) (hb : d338422 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d337536, d338422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337536, d338422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d334890 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d337537 q = 1) (hb : d338423 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d337537, d338423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337537, d338423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d337538 q = 1) (hb : d338431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d337538, d338431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d337538, d338431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d337539 q = 1) (hb : d338432 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d337539, d338432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d337539, d338432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d338153 q = 1) (hb : d338433 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d338153, d338433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338153, d338433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92213 (p : Pattern) (ha : d338164 p = 1) (hb : d338443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d334991 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d338159 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d338160 q = 1) (hb : d338439 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d338160, d338439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338160, d338439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d335076 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d338161 q = 1) (hb : d338440 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d338161, d338440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338161, d338440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d338162 q = 1) (hb : d338441 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d338162, d338441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338162, d338441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d338163 q = 1) (hb : d338442 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d338163, d338442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338163, d338442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d338164 q = 1) (hb : d338443 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d338164, d338443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338164, d338443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92214 (p : Pattern) (ha : d338170 p = 1) (hb : d338449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d334724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337541 q = 1) (hb : d338427 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d337541, d338427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92210 q ha hb
    | true =>
      simp only [d337541, d338427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92211 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d334908 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d337542 q = 1) (hb : d338428 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d337542, d338428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337542, d338428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d338151 q = 1) (hb : d338429 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338151, d338429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338151, d338429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d338152 q = 1) (hb : d338430 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338152, d338430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338152, d338430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d338154 q = 1) (hb : d338434 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d338154, d338434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338154, d338434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92212 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d334917 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d338155 q = 1) (hb : d338435 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d338155, d338435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d338155, d338435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d338156 q = 1) (hb : d338436 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338156, d338436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d338156, d338436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d338157 q = 1) (hb : d338437 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338157, d338437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d338157, d338437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d338158 q = 1) (hb : d338438 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d338158, d338438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d338158, d338438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d338165 q = 1) (hb : d338444 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d338165, d338444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338165, d338444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92213 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d335092 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d338166 q = 1) (hb : d338445 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d338166, d338445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d338166, d338445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d338167 q = 1) (hb : d338446 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338167, d338446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d338167, d338446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d338168 q = 1) (hb : d338447 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338168, d338447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d338168, d338447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d338169 q = 1) (hb : d338448 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d338169, d338448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d338169, d338448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d338170 q = 1) (hb : d338449 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d338170, d338449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d338170, d338449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro92215 (p : Pattern) (ha : d338176 p = 1) (hb : d338455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d338171 q = 1) (hb : d338450 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d338171, d338450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338171, d338450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92214 q ha hb
  have h2 (q : Pattern) (ha : d338172 q = 1) (hb : d338451 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d338172, d338451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338172, d338451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d338173 q = 1) (hb : d338452 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d338173, d338452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338173, d338452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d338174 q = 1) (hb : d338453 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d338174, d338453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338174, d338453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d338175 q = 1) (hb : d338454 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d338175, d338454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338175, d338454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d338176 q = 1) (hb : d338455 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d338176, d338455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338176, d338455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92216 (p : Pattern) (ha : d337835 p = 1) (hb : d338464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d335192 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d335201 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d335218 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d337830 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d337831 q = 1) (hb : d338460 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d337831, d338460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337831, d338460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d335308 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d337832 q = 1) (hb : d338461 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d337832, d338461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d337832, d338461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d337833 q = 1) (hb : d338462 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d337833, d338462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337833, d338462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d337834 q = 1) (hb : d338463 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d337834, d338463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337834, d338463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d337835 q = 1) (hb : d338464 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d337835, d338464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d337835, d338464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro92217 (p : Pattern) (ha : d337845 p = 1) (hb : d338469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d335192 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d335201 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d335218 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d337830 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d337831 q = 1) (hb : d338460 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d337831, d338460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d337831, d338460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d335308 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d337832 q = 1) (hb : d338461 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d337832, d338461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d337832, d338461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d337833 q = 1) (hb : d338462 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d337833, d338462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337833, d338462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d337834 q = 1) (hb : d338463 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d337834, d338463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d337834, d338463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d335318 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d335323 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d335325 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d337840 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d337841 q = 1) (hb : d338465 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d337841, d338465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d337841, d338465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d335332 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d337842 q = 1) (hb : d338466 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d337842, d338466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d337842, d338466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d337843 q = 1) (hb : d338467 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d337843, d338467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d337843, d338467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d337844 q = 1) (hb : d338468 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d337844, d338468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d337844, d338468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d337845 q = 1) (hb : d338469 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d337845, d338469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d337845, d338469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro92218 (p : Pattern) (ha : d338183 p = 1) (hb : d338476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d335325 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d337840 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d337841 q = 1) (hb : d338465 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d337841, d338465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337841, d338465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d335332 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d337842 q = 1) (hb : d338466 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d337842, d338466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d337842, d338466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d337843 q = 1) (hb : d338474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d337843, d338474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d337843, d338474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d337844 q = 1) (hb : d338475 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d337844, d338475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d337844, d338475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d338183 q = 1) (hb : d338476 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d338183, d338476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338183, d338476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92219 (p : Pattern) (ha : d338194 p = 1) (hb : d338486 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d335424 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d338189 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d338190 q = 1) (hb : d338482 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d338190, d338482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338190, d338482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d335500 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d338191 q = 1) (hb : d338483 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d338191, d338483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338191, d338483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d338192 q = 1) (hb : d338484 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d338192, d338484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338192, d338484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d338193 q = 1) (hb : d338485 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d338193, d338485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338193, d338485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d338194 q = 1) (hb : d338486 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d338194, d338486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338194, d338486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92220 (p : Pattern) (ha : d338200 p = 1) (hb : d338492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d335184 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337846 q = 1) (hb : d338470 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d337846, d338470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92216 q ha hb
    | true =>
      simp only [d337846, d338470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92217 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d335350 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d337847 q = 1) (hb : d338471 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d337847, d338471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d337847, d338471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d338181 q = 1) (hb : d338472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338181, d338472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338181, d338472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d338182 q = 1) (hb : d338473 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338182, d338473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338182, d338473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d338184 q = 1) (hb : d338477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d338184, d338477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338184, d338477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92218 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d335359 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d338185 q = 1) (hb : d338478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d338185, d338478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d338185, d338478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d338186 q = 1) (hb : d338479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338186, d338479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d338186, d338479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d338187 q = 1) (hb : d338480 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338187, d338480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d338187, d338480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d338188 q = 1) (hb : d338481 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d338188, d338481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d338188, d338481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d338195 q = 1) (hb : d338487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d338195, d338487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338195, d338487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92219 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d335516 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d338196 q = 1) (hb : d338488 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d338196, d338488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d338196, d338488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d338197 q = 1) (hb : d338489 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338197, d338489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d338197, d338489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d338198 q = 1) (hb : d338490 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338198, d338490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d338198, d338490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d338199 q = 1) (hb : d338491 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d338199, d338491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d338199, d338491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d338200 q = 1) (hb : d338492 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d338200, d338492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d338200, d338492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro92221 (p : Pattern) (ha : d338206 p = 1) (hb : d338498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d338201 q = 1) (hb : d338493 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d338201, d338493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338201, d338493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92220 q ha hb
  have h2 (q : Pattern) (ha : d338202 q = 1) (hb : d338494 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d338202, d338494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338202, d338494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d338203 q = 1) (hb : d338495 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d338203, d338495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338203, d338495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d338204 q = 1) (hb : d338496 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d338204, d338496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338204, d338496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d338205 q = 1) (hb : d338497 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d338205, d338497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338205, d338497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d338206 q = 1) (hb : d338498 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d338206, d338498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338206, d338498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92222 (p : Pattern) (ha : d338212 p = 1) (hb : d338504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d338374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d338148 q = 1) (hb : d338414 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d338148, d338414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338148, d338414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92209 q ha hb
  have h3 (q : Pattern) (ha : d338149 q = 1) (hb : d338415 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d338149, d338415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338149, d338415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d338150 q = 1) (hb : d338416 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d338150, d338416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338150, d338416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d338177 q = 1) (hb : d338456 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d338177, d338456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338177, d338456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92215 q ha hb
  have h6 (q : Pattern) (ha : d338178 q = 1) (hb : d338457 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d338178, d338457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338178, d338457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d338179 q = 1) (hb : d338458 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d338179, d338458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338179, d338458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d338180 q = 1) (hb : d338459 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d338180, d338459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338180, d338459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d338207 q = 1) (hb : d338499 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d338207, d338499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338207, d338499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92221 q ha hb
  have h10 (q : Pattern) (ha : d338208 q = 1) (hb : d338500 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d338208, d338500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338208, d338500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d338209 q = 1) (hb : d338501 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d338209, d338501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338209, d338501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d338210 q = 1) (hb : d338502 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d338210, d338502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338210, d338502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d338211 q = 1) (hb : d338503 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d338211, d338503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d338211, d338503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d338212 q = 1) (hb : d338504 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d338212, d338504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d338212, d338504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h14 p ha hb
theorem andIntro92223 (p : Pattern) (ha : d338218 p = 1) (hb : d338510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d338213 q = 1) (hb : d338505 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d338213, d338505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92222 q ha hb
    | true =>
      simp only [d338213, d338505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d338214 q = 1) (hb : d338506 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d338214, d338506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338214, d338506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d338215 q = 1) (hb : d338507 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d338215, d338507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338215, d338507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d338216 q = 1) (hb : d338508 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d338216, d338508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338216, d338508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d338217 q = 1) (hb : d338509 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d338217, d338509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338217, d338509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d338218 q = 1) (hb : d338510 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d338218, d338510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338218, d338510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro92224 (p : Pattern) (ha : d338224 p = 1) (hb : d338516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d338219 q = 1) (hb : d338511 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d338219, d338511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92223 q ha hb
    | true =>
      simp only [d338219, d338511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d338220 q = 1) (hb : d338512 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d338220, d338512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338220, d338512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d338221 q = 1) (hb : d338513 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d338221, d338513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338221, d338513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d338222 q = 1) (hb : d338514 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d338222, d338514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338222, d338514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d338223 q = 1) (hb : d338515 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d338223, d338515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338223, d338515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d338224 q = 1) (hb : d338516 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d338224, d338516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338224, d338516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro92225 (p : Pattern) (ha : d338230 p = 1) (hb : d338522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d338225 q = 1) (hb : d338517 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d338225, d338517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92224 q ha hb
    | true =>
      simp only [d338225, d338517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d338226 q = 1) (hb : d338518 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d338226, d338518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338226, d338518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d338227 q = 1) (hb : d338519 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d338227, d338519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338227, d338519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d338228 q = 1) (hb : d338520 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d338228, d338520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338228, d338520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d338229 q = 1) (hb : d338521 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d338229, d338521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338229, d338521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d338230 q = 1) (hb : d338522 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d338230, d338522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338230, d338522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro92226 (p : Pattern) (ha : d338236 p = 1) (hb : d338528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d338231 q = 1) (hb : d338523 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d338231, d338523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92225 q ha hb
    | true =>
      simp only [d338231, d338523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d338232 q = 1) (hb : d338524 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d338232, d338524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338232, d338524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d338233 q = 1) (hb : d338525 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d338233, d338525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338233, d338525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d338234 q = 1) (hb : d338526 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d338234, d338526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338234, d338526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d338235 q = 1) (hb : d338527 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d338235, d338527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338235, d338527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d338236 q = 1) (hb : d338528 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d338236, d338528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338236, d338528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro92227 (p : Pattern) (ha : d338242 p = 1) (hb : d338534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d338237 q = 1) (hb : d338529 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d338237, d338529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92226 q ha hb
    | true =>
      simp only [d338237, d338529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d338238 q = 1) (hb : d338530 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d338238, d338530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338238, d338530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d338239 q = 1) (hb : d338531 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d338239, d338531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338239, d338531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d338240 q = 1) (hb : d338532 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d338240, d338532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338240, d338532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d338241 q = 1) (hb : d338533 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d338241, d338533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338241, d338533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d338242 q = 1) (hb : d338534 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d338242, d338534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338242, d338534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro92228 (p : Pattern) (ha : d338248 p = 1) (hb : d338540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d338243 q = 1) (hb : d338535 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d338243, d338535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92227 q ha hb
    | true =>
      simp only [d338243, d338535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d338244 q = 1) (hb : d338536 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d338244, d338536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338244, d338536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d338245 q = 1) (hb : d338537 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d338245, d338537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338245, d338537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d338246 q = 1) (hb : d338538 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d338246, d338538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338246, d338538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d338247 q = 1) (hb : d338539 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d338247, d338539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338247, d338539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d338248 q = 1) (hb : d338540 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d338248, d338540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338248, d338540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro92229 (p : Pattern) (ha : d338254 p = 1) (hb : d338546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d338249 q = 1) (hb : d338541 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d338249, d338541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92228 q ha hb
    | true =>
      simp only [d338249, d338541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d338250 q = 1) (hb : d338542 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d338250, d338542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338250, d338542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d338251 q = 1) (hb : d338543 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d338251, d338543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338251, d338543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d338252 q = 1) (hb : d338544 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d338252, d338544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338252, d338544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d338253 q = 1) (hb : d338545 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d338253, d338545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338253, d338545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d338254 q = 1) (hb : d338546 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d338254, d338546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338254, d338546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro92230 (p : Pattern) (ha : d138 p = 1) (hb : d253269 p = 1) : d40157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d253269 q = 1) : d40152 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73823 q ha hb
    | true =>
      simp only [d133, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d134 q = 1) (hb : d253269 q = 1) : d40153 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d253269 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d135 q = 1) (hb : d253269 q = 1) : d40154 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d40154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d135, d40154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21 q = 1) (hb : d253269 q = 1) : d21 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d136 q = 1) (hb : d253269 q = 1) : d40155 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d40155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d136, d40155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137 q = 1) (hb : d253269 q = 1) : d40156 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d40156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137, d40156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23 q = 1) (hb : d253269 q = 1) : d23 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d138 q = 1) (hb : d253269 q = 1) : d40157 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d138, d40157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d138, d40157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro92231 (p : Pattern) (ha : d144 p = 1) (hb : d253269 p = 1) : d40163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d253269 q = 1) : d40158 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d40158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92230 q ha hb
    | true =>
      simp only [d139, d40158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d140 q = 1) (hb : d253269 q = 1) : d40159 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d40159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140, d40159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d141 q = 1) (hb : d253269 q = 1) : d40160 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d40160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d40160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d253269 q = 1) : d40161 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d40161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d142, d40161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d253269 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d143 q = 1) (hb : d253269 q = 1) : d40162 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d40162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d143, d40162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d253269 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d144 q = 1) (hb : d253269 q = 1) : d40163 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, d40163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144, d40163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92232 (p : Pattern) (ha : d150 p = 1) (hb : d253269 p = 1) : d40169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d253269 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d253269 q = 1) : d40164 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d40164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92231 q ha hb
    | true =>
      simp only [d145, d40164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d253269 q = 1) : d40165 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d40165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d40165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d253269 q = 1) : d40166 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d40166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d40166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d253269 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148 q = 1) (hb : d253269 q = 1) : d40167 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d40167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148, d40167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d253269 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d149 q = 1) (hb : d253269 q = 1) : d40168 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d40168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d149, d40168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150 q = 1) (hb : d253269 q = 1) : d40169 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, d40169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150, d40169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro92233 (p : Pattern) (ha : d203 p = 1) (hb : d253269 p = 1) : d40182 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d253269 q = 1) : d40170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92232 q ha hb
    | true =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d253269 q = 1) : d40171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d253269 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d253269 q = 1) : d40172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d40172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d40172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d253269 q = 1) : d40173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d40173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d40173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d253269 q = 1) : d40174 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d40174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d40174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d203 q = 1) (hb : d253269 q = 1) : d40182 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, d40182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d203, d40182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro92234 (p : Pattern) (ha : d4349 p = 1) (hb : d253269 p = 1) : d289294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d253269 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d253269 q = 1) : d40183 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d40183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92233 q ha hb
    | true =>
      simp only [d204, d40183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4340 q = 1) (hb : d253269 q = 1) : d289283 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d289283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4340, d289283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d253269 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4341 q = 1) (hb : d253269 q = 1) : d289284 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d289284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4341, d289284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4342 q = 1) (hb : d253269 q = 1) : d289292 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d289292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d289292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4343 q = 1) (hb : d253269 q = 1) : d289293 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d289293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d289293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4349 q = 1) (hb : d253269 q = 1) : d289294 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d289294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d289294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92235 (p : Pattern) (ha : d231 p = 1) (hb : d253269 p = 1) : d40206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d253269 q = 1) : d40201 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d40201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d40201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92230 q ha hb
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d253269 q = 1) : d40158 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d40158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92230 q ha hb
    | true =>
      simp only [d139, d40158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d227 q = 1) (hb : d253269 q = 1) : d40202 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d40202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d227, d40202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d253269 q = 1) : d40159 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d40159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d40159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d253269 q = 1) : d40203 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d40203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d40203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d253269 q = 1) : d40204 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d40204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d40204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d253269 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d230 q = 1) (hb : d253269 q = 1) : d40205 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d40205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d230, d40205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d253269 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d231 q = 1) (hb : d253269 q = 1) : d40206 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d40206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d231, d40206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro92236 (p : Pattern) (ha : d237 p = 1) (hb : d253269 p = 1) : d40212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d253269 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d253269 q = 1) : d40207 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d40207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92235 q ha hb
    | true =>
      simp only [d232, d40207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d253269 q = 1) : d40208 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d40208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d40208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d253269 q = 1) : d40209 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d40209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d40209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d253269 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d235 q = 1) (hb : d253269 q = 1) : d40210 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d40210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235, d40210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d253269 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d236 q = 1) (hb : d253269 q = 1) : d40211 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d40211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236, d40211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237 q = 1) (hb : d253269 q = 1) : d40212 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d40212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237, d40212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro92237 (p : Pattern) (ha : d243 p = 1) (hb : d253269 p = 1) : d40218 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d253269 q = 1) : d40213 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d40213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92236 q ha hb
    | true =>
      simp only [d238, d40213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d253269 q = 1) : d40214 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d40214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d40214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d253269 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d240 q = 1) (hb : d253269 q = 1) : d40215 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, d40215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d240, d40215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241 q = 1) (hb : d253269 q = 1) : d40216 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, d40216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d241, d40216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d242 q = 1) (hb : d253269 q = 1) : d40217 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, d40217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242, d40217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d243 q = 1) (hb : d253269 q = 1) : d40218 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, d40218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243, d40218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro92238 (p : Pattern) (ha : d4359 p = 1) (hb : d253269 p = 1) : d289304 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d253269 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d253269 q = 1) : d40219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d40219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92237 q ha hb
    | true =>
      simp only [d244, d40219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4355 q = 1) (hb : d253269 q = 1) : d289300 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d289300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4355, d289300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d253269 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d253269 q = 1) : d289301 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d289301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4356, d289301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d253269 q = 1) : d289302 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d289302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d289302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d253269 q = 1) : d289303 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d289303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d289303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d253269 q = 1) : d289304 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d289304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d289304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92239 (p : Pattern) (ha : d156 p = 1) (hb : d253269 p = 1) : d40175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d253269 q = 1) : d40170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92232 q ha hb
    | true =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d253269 q = 1) : d40171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d253269 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d253269 q = 1) : d40172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d40172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d40172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d253269 q = 1) : d40173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d40173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d40173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d253269 q = 1) : d40174 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d40174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d40174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d156 q = 1) (hb : d253269 q = 1) : d40175 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, d40175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, d40175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro92240 (p : Pattern) (ha : d51643 p = 1) (hb : d253269 p = 1) : d289282 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d253269 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d253269 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d253269 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157 q = 1) (hb : d253269 q = 1) : d40176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d40176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92239 q ha hb
    | true =>
      simp only [d157, d40176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d253269 q = 1) : d289278 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d289278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4335, d289278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d253269 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d253269 q = 1) : d289279 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d289279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d289279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d253269 q = 1) : d289280 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d289280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51641, d289280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d253269 q = 1) : d289281 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d289281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51642, d289281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51643 q = 1) (hb : d253269 q = 1) : d289282 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d289282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d289282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro92241 (p : Pattern) (ha : d51646 p = 1) (hb : d253269 p = 1) : d289287 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d253269 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d253269 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d253269 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d253269 q = 1) : d40176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d40176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92239 q ha hb
    | true =>
      simp only [d157, d40176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d253269 q = 1) : d289278 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d289278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4335, d289278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d253269 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d253269 q = 1) : d289279 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d289279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d289279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d253269 q = 1) : d289280 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d289280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51641, d289280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d253269 q = 1) : d289281 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d289281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51642, d289281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d253269 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d253269 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d253269 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d204 q = 1) (hb : d253269 q = 1) : d40183 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d40183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92233 q ha hb
    | true =>
      simp only [d204, d40183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4340 q = 1) (hb : d253269 q = 1) : d289283 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d289283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4340, d289283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d253269 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d4341 q = 1) (hb : d253269 q = 1) : d289284 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d289284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4341, d289284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51644 q = 1) (hb : d253269 q = 1) : d289285 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d289285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51644, d289285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51645 q = 1) (hb : d253269 q = 1) : d289286 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d289286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51645, d289286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51646 q = 1) (hb : d253269 q = 1) : d289287 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d289287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51646, d289287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro92242 (p : Pattern) (ha : d51652 p = 1) (hb : d253269 p = 1) : d289310 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d253269 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51647 q = 1) (hb : d253269 q = 1) : d289288 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d289288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92240 q ha hb
    | true =>
      simp only [d51647, d289288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92241 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d253269 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51648 q = 1) (hb : d253269 q = 1) : d289289 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d289289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51648, d289289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51649 q = 1) (hb : d253269 q = 1) : d289290 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d289290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51649, d289290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51650 q = 1) (hb : d253269 q = 1) : d289291 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d289291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51650, d289291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4350 q = 1) (hb : d253269 q = 1) : d289295 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d289295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4350, d289295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92234 q ha hb
  have h8 (q : Pattern) (ha : d4351 q = 1) (hb : d253269 q = 1) : d289296 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d289296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4351, d289296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d4352 q = 1) (hb : d253269 q = 1) : d289297 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d289297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4352, d289297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4353 q = 1) (hb : d253269 q = 1) : d289298 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d289298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4353, d289298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d51651 q = 1) (hb : d253269 q = 1) : d289299 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d289299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51651, d289299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4360 q = 1) (hb : d253269 q = 1) : d289305 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d289305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4360, d289305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92238 q ha hb
  have h13 (q : Pattern) (ha : d4361 q = 1) (hb : d253269 q = 1) : d289306 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d289306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4361, d289306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d4362 q = 1) (hb : d253269 q = 1) : d289307 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d289307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4362, d289307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d4363 q = 1) (hb : d253269 q = 1) : d289308 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d289308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4363, d289308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d4364 q = 1) (hb : d253269 q = 1) : d289309 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d289309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4364, d289309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d51652 q = 1) (hb : d253269 q = 1) : d289310 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d289310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51652, d289310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro92243 (p : Pattern) (ha : d284 p = 1) (hb : d253269 p = 1) : d40240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d253269 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d253269 q = 1) : d40176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d40176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92239 q ha hb
    | true =>
      simp only [d157, d40176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d253269 q = 1) : d40236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d40236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d40236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d253269 q = 1) : d40237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d40237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d40237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d253269 q = 1) : d40238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d40238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d40238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d253269 q = 1) : d40239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d40239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d40239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284 q = 1) (hb : d253269 q = 1) : d40240 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d40240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d40240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro92244 (p : Pattern) (ha : d291 p = 1) (hb : d253269 p = 1) : d40247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d253269 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d253269 q = 1) : d40176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d40176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92239 q ha hb
    | true =>
      simp only [d157, d40176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d253269 q = 1) : d40236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d40236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d40236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d253269 q = 1) : d40237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d40237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d40237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d253269 q = 1) : d40238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d40238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d40238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d253269 q = 1) : d40239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d40239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d40239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d253269 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d204 q = 1) (hb : d253269 q = 1) : d40183 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d40183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92233 q ha hb
    | true =>
      simp only [d204, d40183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287 q = 1) (hb : d253269 q = 1) : d40243 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d40243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d40243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288 q = 1) (hb : d253269 q = 1) : d40244 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d40244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288, d40244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d289 q = 1) (hb : d253269 q = 1) : d40245 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d40245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d40245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d290 q = 1) (hb : d253269 q = 1) : d40246 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d40246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d40246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d291 q = 1) (hb : d253269 q = 1) : d40247 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d40247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d291, d40247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro92245 (p : Pattern) (ha : d397 p = 1) (hb : d253269 p = 1) : d40359 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d253269 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d253269 q = 1) : d40176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d40176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92239 q ha hb
    | true =>
      simp only [d157, d40176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d253269 q = 1) : d40236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d40236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d40236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d253269 q = 1) : d40237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d40237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d40237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d253269 q = 1) : d40238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d40238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d40238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d253269 q = 1) : d40239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d40239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d40239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d253269 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d397 q = 1) (hb : d253269 q = 1) : d40359 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, d40359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d397, d40359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro92246 (p : Pattern) (ha : d296 p = 1) (hb : d253269 p = 1) : d40252 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d253269 q = 1) : d40170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92232 q ha hb
    | true =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d253269 q = 1) : d40171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d253269 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d253269 q = 1) : d40172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d40172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d40172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d253269 q = 1) : d40173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d40173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d40173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d253269 q = 1) : d40251 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d40251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d40251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d296 q = 1) (hb : d253269 q = 1) : d40252 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d296, d40252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d296, d40252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro92247 (p : Pattern) (ha : d303 p = 1) (hb : d253269 p = 1) : d40259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d253269 q = 1) : d40170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92232 q ha hb
    | true =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d253269 q = 1) : d40171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d253269 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d253269 q = 1) : d40172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d40172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d40172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d253269 q = 1) : d40257 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d40257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d40257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d253269 q = 1) : d40258 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d40258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d40258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d303 q = 1) (hb : d253269 q = 1) : d40259 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, d40259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, d40259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro92248 (p : Pattern) (ha : d4736 p = 1) (hb : d253269 p = 1) : d40330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d253269 q = 1) : d40170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92232 q ha hb
    | true =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d253269 q = 1) : d40171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d253269 q = 1) : d40327 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d40327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d40327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d253269 q = 1) : d40328 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d40328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d40328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d253269 q = 1) : d40329 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d40329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d40329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4736 q = 1) (hb : d253269 q = 1) : d40330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, d40330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, d40330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro92249 (p : Pattern) (ha : d318 p = 1) (hb : d253269 p = 1) : d40270 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d253269 q = 1) : d40265 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73843 q ha hb
    | true =>
      simp only [d313, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d314 q = 1) (hb : d253269 q = 1) : d40266 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d133 q = 1) (hb : d253269 q = 1) : d40152 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73823 q ha hb
    | true =>
      simp only [d133, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d134 q = 1) (hb : d253269 q = 1) : d40153 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d315 q = 1) (hb : d253269 q = 1) : d40267 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d40267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315, d40267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20 q = 1) (hb : d253269 q = 1) : d20 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d135 q = 1) (hb : d253269 q = 1) : d40154 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d40154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d135, d40154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d316 q = 1) (hb : d253269 q = 1) : d40268 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d40268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316, d40268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d317 q = 1) (hb : d253269 q = 1) : d40269 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d40269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d317, d40269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21 q = 1) (hb : d253269 q = 1) : d21 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d136 q = 1) (hb : d253269 q = 1) : d40155 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d40155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d136, d40155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d137 q = 1) (hb : d253269 q = 1) : d40156 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d40156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137, d40156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d318 q = 1) (hb : d253269 q = 1) : d40270 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d318, d40270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d318, d40270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
end NetHack.Soko22Hazard87
