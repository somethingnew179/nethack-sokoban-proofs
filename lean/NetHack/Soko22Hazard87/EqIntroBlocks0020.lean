import NetHack.Soko22Hazard87.EqIntroBlocks0019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro5000 (p : Pattern) (selected : d86131 p = 0) : d87335 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86126 q = 0) : d87330 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86126, d87330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86126, d87330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro344 q selected
  have h2 (q : Pattern) (selected : d86127 q = 0) : d87331 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86127, d87331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86127, d87331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86128 q = 0) : d87332 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86128, d87332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86128, d87332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro345 q selected
  have h4 (q : Pattern) (selected : d86129 q = 0) : d87333 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86129, d87333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86129, d87333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86130 q = 0) : d87334 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86130, d87334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86130, d87334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86131 q = 0) : d87335 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86131, d87335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86131, d87335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5001 (p : Pattern) (selected : d86135 p = 0) : d87339 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86128 q = 0) : d87332 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86128, d87332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86128, d87332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro345 q selected
  have h2 (q : Pattern) (selected : d86129 q = 0) : d87333 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86129, d87333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86129, d87333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86134 q = 0) : d87338 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86134, d87338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86134, d87338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86135 q = 0) : d87339 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86135, d87339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86135, d87339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5002 (p : Pattern) (selected : d86141 p = 0) : d87345 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86132 q = 0) : d87336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86132, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5000 q selected
    | true =>
      simp only [d86132, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86133 q = 0) : d87337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86133, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86133, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86136 q = 0) : d87340 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86136, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5001 q selected
    | true =>
      simp only [d86136, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86137 q = 0) : d87341 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86137, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86137, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86138 q = 0) : d87342 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86138, d87342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86138, d87342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86139 q = 0) : d87343 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86139, d87343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86139, d87343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86140 q = 0) : d87344 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86140, d87344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86140, d87344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86141 q = 0) : d87345 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86141, d87345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86141, d87345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5003 (p : Pattern) (selected : d86145 p = 0) : d87349 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86136 q = 0) : d87340 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86136, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5001 q selected
    | true =>
      simp only [d86136, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86137 q = 0) : d87341 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86137, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86137, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86142 q = 0) : d87346 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86142, d87346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86142, d87346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86143 q = 0) : d87347 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86143, d87347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86143, d87347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86144 q = 0) : d87348 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86144, d87348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86144, d87348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86145 q = 0) : d87349 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86145, d87349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86145, d87349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5004 (p : Pattern) (selected : d86151 p = 0) : d87401 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86065 q = 0) : d87336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86065, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4986 q selected
    | true =>
      simp only [d86065, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86066 q = 0) : d87337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86066, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86066, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86148 q = 0) : d87398 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86148, d87398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86148, d87398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86149 q = 0) : d87399 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86149, d87399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86149, d87399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86150 q = 0) : d87400 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86150, d87400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86150, d87400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86151 q = 0) : d87401 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86151, d87401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86151, d87401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5005 (p : Pattern) (selected : d86157 p = 0) : d87407 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86102 q = 0) : d87373 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86102, d87373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4994 q selected
    | true =>
      simp only [d86102, d87373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4995 q selected
  have h2 (q : Pattern) (selected : d86103 q = 0) : d87374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86103, d87374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86103, d87374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86104 q = 0) : d87375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86104, d87375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86104, d87375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86105 q = 0) : d87376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86105, d87376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86105, d87376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86112 q = 0) : d87383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86112, d87383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4996 q selected
    | true =>
      simp only [d86112, d87383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4997 q selected
  have h6 (q : Pattern) (selected : d86113 q = 0) : d87384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86113, d87384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86113, d87384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86114 q = 0) : d87385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86114, d87385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86114, d87385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86125 q = 0) : d87396 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86125, d87396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4999 q selected
    | true =>
      simp only [d86125, d87396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4988 q selected
  have h9 (q : Pattern) (selected : d86146 q = 0) : d87350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86146, d87350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5002 q selected
    | true =>
      simp only [d86146, d87350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5003 q selected
  have h10 (q : Pattern) (selected : d86147 q = 0) : d87397 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86147, d87397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d86147, d87397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86152 q = 0) : d87402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86152, d87402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5004 q selected
    | true =>
      simp only [d86152, d87402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d86153 q = 0) : d87403 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86153, d87403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d86153, d87403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d86154 q = 0) : d87404 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86154, d87404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86154, d87404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d86155 q = 0) : d87405 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86155, d87405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86155, d87405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d86156 q = 0) : d87406 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86156, d87406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86156, d87406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d86157 q = 0) : d87407 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86157, d87407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86157, d87407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro5006 (p : Pattern) (selected : d86158 p = 0) : d87408 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86065 q = 0) : d87336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86065, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4986 q selected
    | true =>
      simp only [d86065, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86066 q = 0) : d87337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86066, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86066, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86069 q = 0) : d87340 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4987 q selected
    | true =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86070 q = 0) : d87341 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86071 q = 0) : d87342 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86071, d87342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86071, d87342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86072 q = 0) : d87343 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86072, d87343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86072, d87343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86098 q = 0) : d87369 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86098, d87369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86098, d87369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86158 q = 0) : d87408 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86158, d87408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86158, d87408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5007 (p : Pattern) (selected : d86159 p = 0) : d87409 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86069 q = 0) : d87340 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4987 q selected
    | true =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86070 q = 0) : d87341 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86075 q = 0) : d87346 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86075, d87346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86075, d87346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86076 q = 0) : d87347 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86076, d87347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86076, d87347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86100 q = 0) : d87371 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86100, d87371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86100, d87371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86159 q = 0) : d87409 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86159, d87409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86159, d87409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5008 (p : Pattern) (selected : d86164 p = 0) : d87414 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86065 q = 0) : d87336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86065, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4986 q selected
    | true =>
      simp only [d86065, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86066 q = 0) : d87337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86066, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86066, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86069 q = 0) : d87340 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4987 q selected
    | true =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86070 q = 0) : d87341 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86071 q = 0) : d87342 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86071, d87342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86071, d87342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86106 q = 0) : d87377 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86106, d87377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86106, d87377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86107 q = 0) : d87378 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86107, d87378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86107, d87378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86164 q = 0) : d87414 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86164, d87414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86164, d87414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5009 (p : Pattern) (selected : d86165 p = 0) : d87415 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86069 q = 0) : d87340 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4987 q selected
    | true =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86070 q = 0) : d87341 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86075 q = 0) : d87346 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86075, d87346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86075, d87346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86109 q = 0) : d87380 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86109, d87380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86109, d87380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86110 q = 0) : d87381 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86110, d87381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86110, d87381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86165 q = 0) : d87415 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86165, d87415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86165, d87415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5010 (p : Pattern) (selected : d86169 p = 0) : d87419 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86119 q = 0) : d87390 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86119, d87390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4998 q selected
    | true =>
      simp only [d86119, d87390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86120 q = 0) : d87391 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86120, d87391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86120, d87391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86065 q = 0) : d87336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86065, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4986 q selected
    | true =>
      simp only [d86065, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86066 q = 0) : d87337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86066, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86066, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86121 q = 0) : d87392 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86121, d87392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86121, d87392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86122 q = 0) : d87393 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86122, d87393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86122, d87393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86123 q = 0) : d87394 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86123, d87394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86123, d87394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86169 q = 0) : d87419 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86169, d87419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86169, d87419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5011 (p : Pattern) (selected : d86171 p = 0) : d87358 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86132 q = 0) : d87336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86132, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5000 q selected
    | true =>
      simp only [d86132, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86133 q = 0) : d87337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86133, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86133, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86136 q = 0) : d87340 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86136, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5001 q selected
    | true =>
      simp only [d86136, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86137 q = 0) : d87341 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86137, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86137, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86138 q = 0) : d87342 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86138, d87342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86138, d87342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86139 q = 0) : d87343 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86139, d87343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86139, d87343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86140 q = 0) : d87344 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86140, d87344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86140, d87344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86171 q = 0) : d87358 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86171, d87358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86171, d87358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5012 (p : Pattern) (selected : d86172 p = 0) : d87359 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86136 q = 0) : d87340 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86136, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5001 q selected
    | true =>
      simp only [d86136, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86137 q = 0) : d87341 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86137, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86137, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86142 q = 0) : d87346 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86142, d87346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86142, d87346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86143 q = 0) : d87347 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86143, d87347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86143, d87347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86144 q = 0) : d87348 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86144, d87348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86144, d87348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86172 q = 0) : d87359 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86172, d87359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86172, d87359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5013 (p : Pattern) (selected : d86175 p = 0) : d87422 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86065 q = 0) : d87336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86065, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4986 q selected
    | true =>
      simp only [d86065, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86066 q = 0) : d87337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86066, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86066, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86148 q = 0) : d87398 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86148, d87398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86148, d87398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86149 q = 0) : d87399 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86149, d87399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86149, d87399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86150 q = 0) : d87400 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86150, d87400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86150, d87400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86175 q = 0) : d87422 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86175, d87422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86175, d87422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5014 (p : Pattern) (selected : d86181 p = 0) : d87428 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86102 q = 0) : d87373 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86102, d87373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4994 q selected
    | true =>
      simp only [d86102, d87373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4995 q selected
  have h2 (q : Pattern) (selected : d86103 q = 0) : d87374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86103, d87374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86103, d87374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86104 q = 0) : d87375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86104, d87375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86104, d87375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86105 q = 0) : d87376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86105, d87376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86105, d87376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86112 q = 0) : d87383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86112, d87383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4996 q selected
    | true =>
      simp only [d86112, d87383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4997 q selected
  have h6 (q : Pattern) (selected : d86113 q = 0) : d87384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86113, d87384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86113, d87384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86114 q = 0) : d87385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86114, d87385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86114, d87385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86125 q = 0) : d87396 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86125, d87396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4999 q selected
    | true =>
      simp only [d86125, d87396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4988 q selected
  have h9 (q : Pattern) (selected : d86146 q = 0) : d87350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86146, d87350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5002 q selected
    | true =>
      simp only [d86146, d87350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5003 q selected
  have h10 (q : Pattern) (selected : d86147 q = 0) : d87397 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86147, d87397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d86147, d87397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86152 q = 0) : d87402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86152, d87402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5004 q selected
    | true =>
      simp only [d86152, d87402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d86153 q = 0) : d87403 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86153, d87403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d86153, d87403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d86154 q = 0) : d87404 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86154, d87404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86154, d87404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d86155 q = 0) : d87405 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86155, d87405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86155, d87405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d86156 q = 0) : d87406 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86156, d87406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86156, d87406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d86160 q = 0) : d87410 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86160, d87410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5006 q selected
    | true =>
      simp only [d86160, d87410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5007 q selected
  have h17 (q : Pattern) (selected : d86161 q = 0) : d87411 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86161, d87411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86161, d87411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d86162 q = 0) : d87412 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86162, d87412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d86162, d87412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d86163 q = 0) : d87413 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86163, d87413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86163, d87413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d86166 q = 0) : d87416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86166, d87416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5008 q selected
    | true =>
      simp only [d86166, d87416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5009 q selected
  have h21 (q : Pattern) (selected : d86167 q = 0) : d87417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86167, d87417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86167, d87417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d86168 q = 0) : d87418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86168, d87418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d86168, d87418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d86170 q = 0) : d87420 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86170, d87420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5010 q selected
    | true =>
      simp only [d86170, d87420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4991 q selected
  have h24 (q : Pattern) (selected : d86173 q = 0) : d87360 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86173, d87360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5011 q selected
    | true =>
      simp only [d86173, d87360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5012 q selected
  have h25 (q : Pattern) (selected : d86174 q = 0) : d87421 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86174, d87421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d86174, d87421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d86176 q = 0) : d87423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86176, d87423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5013 q selected
    | true =>
      simp only [d86176, d87423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d86177 q = 0) : d87424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86177, d87424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d86177, d87424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d86178 q = 0) : d87425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86178, d87425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d86178, d87425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d86179 q = 0) : d87426 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86179, d87426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d86179, d87426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d86180 q = 0) : d87427 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86180, d87427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d86180, d87427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d86181 q = 0) : d87428 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86181, d87428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d86181, d87428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro5015 (p : Pattern) (selected : d86188 p = 0) : d87435 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86079 q = 0) : d87350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86079, d87350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4988 q selected
    | true =>
      simp only [d86079, d87350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4989 q selected
  have h2 (q : Pattern) (selected : d86080 q = 0) : d87351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86080, d87351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86080, d87351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86081 q = 0) : d87352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86081, d87352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86081, d87352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86082 q = 0) : d87353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86082, d87353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86082, d87353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86083 q = 0) : d87354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86083, d87354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86083, d87354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86183 q = 0) : d87430 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86183, d87430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4989 q selected
    | true =>
      simp only [d86183, d87430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86184 q = 0) : d87431 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86184, d87431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86184, d87431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86185 q = 0) : d87432 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86185, d87432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86185, d87432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d86186 q = 0) : d87433 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86186, d87433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86186, d87433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86187 q = 0) : d87434 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86187, d87434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86187, d87434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86188 q = 0) : d87435 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86188, d87435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86188, d87435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5016 (p : Pattern) (selected : d86194 p = 0) : d87441 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86183 q = 0) : d87430 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86183, d87430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4989 q selected
    | true =>
      simp only [d86183, d87430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86184 q = 0) : d87431 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86184, d87431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86184, d87431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86185 q = 0) : d87432 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86185, d87432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86185, d87432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86186 q = 0) : d87433 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86186, d87433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86186, d87433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86187 q = 0) : d87434 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86187, d87434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86187, d87434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86189 q = 0) : d87436 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86189, d87436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4992 q selected
    | true =>
      simp only [d86189, d87436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86190 q = 0) : d87437 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86190, d87437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86190, d87437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86191 q = 0) : d87438 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86191, d87438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86191, d87438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d86192 q = 0) : d87439 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86192, d87439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86192, d87439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86193 q = 0) : d87440 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86193, d87440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86193, d87440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86194 q = 0) : d87441 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86194, d87441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86194, d87441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5017 (p : Pattern) (selected : d86201 p = 0) : d87448 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86170 q = 0) : d87420 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86170, d87420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5010 q selected
    | true =>
      simp only [d86170, d87420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4991 q selected
  have h2 (q : Pattern) (selected : d86173 q = 0) : d87360 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86173, d87360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5011 q selected
    | true =>
      simp only [d86173, d87360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5012 q selected
  have h3 (q : Pattern) (selected : d86174 q = 0) : d87421 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86174, d87421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86174, d87421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86176 q = 0) : d87423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86176, d87423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5013 q selected
    | true =>
      simp only [d86176, d87423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86177 q = 0) : d87424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86177, d87424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86177, d87424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86178 q = 0) : d87425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86178, d87425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86178, d87425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86199 q = 0) : d87446 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86199, d87446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86199, d87446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86200 q = 0) : d87447 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86200, d87447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86200, d87447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86201 q = 0) : d87448 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86201, d87448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86201, d87448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro5018 (p : Pattern) (selected : d86203 p = 0) : d87450 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86189 q = 0) : d87436 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86189, d87436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4992 q selected
    | true =>
      simp only [d86189, d87436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86190 q = 0) : d87437 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86190, d87437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86190, d87437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86191 q = 0) : d87438 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86191, d87438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86191, d87438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86192 q = 0) : d87439 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86192, d87439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86192, d87439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86193 q = 0) : d87440 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86193, d87440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86193, d87440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86203 q = 0) : d87450 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86203, d87450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86203, d87450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5019 (p : Pattern) (selected : d86214 p = 0) : d87461 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86209 q = 0) : d87456 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86209, d87456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86209, d87456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro364 q selected
  have h2 (q : Pattern) (selected : d86210 q = 0) : d87457 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86210, d87457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86210, d87457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86211 q = 0) : d87458 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86211, d87458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86211, d87458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro365 q selected
  have h4 (q : Pattern) (selected : d86212 q = 0) : d87459 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86212, d87459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86212, d87459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86213 q = 0) : d87460 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86213, d87460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86213, d87460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86214 q = 0) : d87461 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86214, d87461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86214, d87461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5020 (p : Pattern) (selected : d86220 p = 0) : d87467 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86211 q = 0) : d87458 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86211, d87458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86211, d87458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro365 q selected
  have h2 (q : Pattern) (selected : d86212 q = 0) : d87459 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86212, d87459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86212, d87459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86217 q = 0) : d87464 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86217, d87464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86217, d87464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro366 q selected
  have h4 (q : Pattern) (selected : d86218 q = 0) : d87465 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86218, d87465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86218, d87465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86219 q = 0) : d87466 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86219, d87466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86219, d87466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86220 q = 0) : d87467 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86220, d87467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86220, d87467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5021 (p : Pattern) (selected : d86226 p = 0) : d87473 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86215 q = 0) : d87462 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86215, d87462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5019 q selected
    | true =>
      simp only [d86215, d87462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86216 q = 0) : d87463 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86216, d87463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86216, d87463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86221 q = 0) : d87468 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86221, d87468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5020 q selected
    | true =>
      simp only [d86221, d87468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86222 q = 0) : d87469 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86222, d87469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86222, d87469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86223 q = 0) : d87470 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86223, d87470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86223, d87470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86224 q = 0) : d87471 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86224, d87471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86224, d87471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86225 q = 0) : d87472 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86225, d87472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86225, d87472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86226 q = 0) : d87473 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86226, d87473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86226, d87473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5022 (p : Pattern) (selected : d86228 p = 0) : d87475 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86217 q = 0) : d87464 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86217, d87464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86217, d87464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro366 q selected
  have h2 (q : Pattern) (selected : d86218 q = 0) : d87465 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86218, d87465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86218, d87465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86227 q = 0) : d87474 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86227, d87474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86227, d87474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86228 q = 0) : d87475 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86228, d87475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86228, d87475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5023 (p : Pattern) (selected : d86234 p = 0) : d87481 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86221 q = 0) : d87468 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86221, d87468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5020 q selected
    | true =>
      simp only [d86221, d87468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86222 q = 0) : d87469 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86222, d87469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86222, d87469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86229 q = 0) : d87476 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86229, d87476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5022 q selected
    | true =>
      simp only [d86229, d87476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86230 q = 0) : d87477 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86230, d87477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86230, d87477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86231 q = 0) : d87478 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86231, d87478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86231, d87478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86232 q = 0) : d87479 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86232, d87479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86232, d87479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86233 q = 0) : d87480 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86233, d87480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86233, d87480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86234 q = 0) : d87481 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86234, d87481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86234, d87481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5024 (p : Pattern) (selected : d86241 p = 0) : d87467 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86236 q = 0) : d87458 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86236, d87458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86236, d87458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro373 q selected
  have h2 (q : Pattern) (selected : d86237 q = 0) : d87459 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86237, d87459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86237, d87459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86238 q = 0) : d87464 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86238, d87464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86238, d87464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro374 q selected
  have h4 (q : Pattern) (selected : d86239 q = 0) : d87465 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86239, d87465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86239, d87465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86240 q = 0) : d87466 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86240, d87466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86240, d87466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86241 q = 0) : d87467 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86241, d87467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86241, d87467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5025 (p : Pattern) (selected : d86245 p = 0) : d87475 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86238 q = 0) : d87464 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86238, d87464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86238, d87464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro374 q selected
  have h2 (q : Pattern) (selected : d86239 q = 0) : d87465 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86239, d87465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86239, d87465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86244 q = 0) : d87474 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86244, d87474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86244, d87474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86245 q = 0) : d87475 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86245, d87475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86245, d87475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5026 (p : Pattern) (selected : d86251 p = 0) : d87481 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86242 q = 0) : d87468 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86242, d87468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5024 q selected
    | true =>
      simp only [d86242, d87468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86243 q = 0) : d87469 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86243, d87469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86243, d87469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86246 q = 0) : d87476 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86246, d87476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5025 q selected
    | true =>
      simp only [d86246, d87476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86247 q = 0) : d87477 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86247, d87477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86247, d87477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86248 q = 0) : d87478 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86248, d87478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86248, d87478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86249 q = 0) : d87479 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86249, d87479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86249, d87479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86250 q = 0) : d87480 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86250, d87480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86250, d87480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86251 q = 0) : d87481 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86251, d87481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86251, d87481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5027 (p : Pattern) (selected : d86255 p = 0) : d87486 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86246 q = 0) : d87476 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86246, d87476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5025 q selected
    | true =>
      simp only [d86246, d87476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86247 q = 0) : d87477 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86247, d87477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86247, d87477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86252 q = 0) : d87483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86252, d87483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86252, d87483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86253 q = 0) : d87484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86253, d87484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86253, d87484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86254 q = 0) : d87485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86254, d87485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86254, d87485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86255 q = 0) : d87486 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86255, d87486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86255, d87486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5028 (p : Pattern) (selected : d86261 p = 0) : d87492 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86221 q = 0) : d87468 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86221, d87468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5020 q selected
    | true =>
      simp only [d86221, d87468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86222 q = 0) : d87469 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86222, d87469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86222, d87469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86258 q = 0) : d87489 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86258, d87489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86258, d87489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86259 q = 0) : d87490 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86259, d87490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86259, d87490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86260 q = 0) : d87491 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86260, d87491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86260, d87491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86261 q = 0) : d87492 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86261, d87492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86261, d87492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5029 (p : Pattern) (selected : d86267 p = 0) : d87498 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86235 q = 0) : d87482 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86235, d87482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5021 q selected
    | true =>
      simp only [d86235, d87482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5023 q selected
  have h2 (q : Pattern) (selected : d86256 q = 0) : d87487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86256, d87487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5026 q selected
    | true =>
      simp only [d86256, d87487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5027 q selected
  have h3 (q : Pattern) (selected : d86257 q = 0) : d87488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86257, d87488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86257, d87488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86262 q = 0) : d87493 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86262, d87493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5028 q selected
    | true =>
      simp only [d86262, d87493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86263 q = 0) : d87494 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86263, d87494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86263, d87494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86264 q = 0) : d87495 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86264, d87495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86264, d87495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86265 q = 0) : d87496 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86265, d87496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86265, d87496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86266 q = 0) : d87497 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86266, d87497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86266, d87497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86267 q = 0) : d87498 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86267, d87498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86267, d87498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro5030 (p : Pattern) (selected : d86272 p = 0) : d87486 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86229 q = 0) : d87476 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86229, d87476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5022 q selected
    | true =>
      simp only [d86229, d87476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86230 q = 0) : d87477 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86230, d87477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86230, d87477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86269 q = 0) : d87483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86269, d87483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86269, d87483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86270 q = 0) : d87484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86270, d87484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86270, d87484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86271 q = 0) : d87485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86271, d87485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86271, d87485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86272 q = 0) : d87486 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86272, d87486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86272, d87486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5031 (p : Pattern) (selected : d86278 p = 0) : d87505 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86273 q = 0) : d87500 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86273, d87500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5030 q selected
    | true =>
      simp only [d86273, d87500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86274 q = 0) : d87501 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86274, d87501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86274, d87501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86275 q = 0) : d87502 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86275, d87502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86275, d87502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86276 q = 0) : d87503 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86276, d87503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86276, d87503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86277 q = 0) : d87504 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86277, d87504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86277, d87504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86278 q = 0) : d87505 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86278, d87505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86278, d87505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5032 (p : Pattern) (selected : d86284 p = 0) : d87511 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86085 q = 0) : d87356 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86085, d87356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86085, d87356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4990 q selected
  have h2 (q : Pattern) (selected : d86086 q = 0) : d87357 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86086, d87357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86086, d87357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d86095 q = 0) : d87366 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86095, d87366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4990 q selected
    | true =>
      simp only [d86095, d87366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4993 q selected
  have h4 (q : Pattern) (selected : d86096 q = 0) : d87367 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86096, d87367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86096, d87367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86097 q = 0) : d87368 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86097, d87368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86097, d87368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86182 q = 0) : d87429 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86182, d87429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5005 q selected
    | true =>
      simp only [d86182, d87429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5014 q selected
  have h7 (q : Pattern) (selected : d86195 q = 0) : d87442 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86195, d87442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5015 q selected
    | true =>
      simp only [d86195, d87442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5016 q selected
  have h8 (q : Pattern) (selected : d86196 q = 0) : d87443 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86196, d87443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86196, d87443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86197 q = 0) : d87444 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86197, d87444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d86197, d87444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d86198 q = 0) : d87445 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86198, d87445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86198, d87445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86202 q = 0) : d87449 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86202, d87449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86202, d87449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5017 q selected
  have h12 (q : Pattern) (selected : d86204 q = 0) : d87451 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86204, d87451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86204, d87451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5018 q selected
  have h13 (q : Pattern) (selected : d86205 q = 0) : d87452 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86205, d87452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d86205, d87452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d86206 q = 0) : d87453 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86206, d87453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d86206, d87453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d86207 q = 0) : d87454 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86207, d87454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d86207, d87454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d86208 q = 0) : d87455 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d86208, d87455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86208, d87455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d86268 q = 0) : d87499 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86268, d87499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86268, d87499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5029 q selected
  have h18 (q : Pattern) (selected : d86279 q = 0) : d87506 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86279, d87506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86279, d87506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5031 q selected
  have h19 (q : Pattern) (selected : d86280 q = 0) : d87507 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86280, d87507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d86280, d87507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d86281 q = 0) : d87508 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86281, d87508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d86281, d87508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d86282 q = 0) : d87509 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86282, d87509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d86282, d87509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d86283 q = 0) : d87510 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d86283, d87510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d86283, d87510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d86284 q = 0) : d87511 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d86284, d87511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d86284, d87511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro5033 (p : Pattern) (selected : d86290 p = 0) : d87517 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86285 q = 0) : d87512 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d86285, d87512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86285, d87512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5032 q selected
  have h2 (q : Pattern) (selected : d86286 q = 0) : d87513 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d86286, d87513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86286, d87513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86287 q = 0) : d87514 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d86287, d87514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86287, d87514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86288 q = 0) : d87515 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d86288, d87515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86288, d87515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86289 q = 0) : d87516 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d86289, d87516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86289, d87516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86290 q = 0) : d87517 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d86290, d87517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86290, d87517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5034 (p : Pattern) (selected : d86298 p = 0) : d87525 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86293 q = 0) : d87520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86293, d87520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86293, d87520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro390 q selected
  have h2 (q : Pattern) (selected : d86294 q = 0) : d87521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86294, d87521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86294, d87521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86295 q = 0) : d87522 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86295, d87522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86295, d87522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro392 q selected
  have h4 (q : Pattern) (selected : d86296 q = 0) : d87523 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86296, d87523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86296, d87523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86297 q = 0) : d87524 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86297, d87524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86297, d87524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86298 q = 0) : d87525 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86298, d87525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86298, d87525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5035 (p : Pattern) (selected : d86302 p = 0) : d87529 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86295 q = 0) : d87522 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86295, d87522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86295, d87522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro392 q selected
  have h2 (q : Pattern) (selected : d86296 q = 0) : d87523 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86296, d87523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86296, d87523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86301 q = 0) : d87528 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86301, d87528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86301, d87528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86302 q = 0) : d87529 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86302, d87529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86302, d87529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5036 (p : Pattern) (selected : d86308 p = 0) : d87535 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86299 q = 0) : d87526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86299, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5034 q selected
    | true =>
      simp only [d86299, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86300 q = 0) : d87527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86300, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86300, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86303 q = 0) : d87530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5035 q selected
    | true =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86304 q = 0) : d87531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86305 q = 0) : d87532 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86305, d87532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86305, d87532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86306 q = 0) : d87533 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86306, d87533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86306, d87533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86307 q = 0) : d87534 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86307, d87534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86307, d87534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86308 q = 0) : d87535 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86308, d87535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86308, d87535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5037 (p : Pattern) (selected : d86312 p = 0) : d87539 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86303 q = 0) : d87530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5035 q selected
    | true =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86304 q = 0) : d87531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86309 q = 0) : d87536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86309, d87536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86309, d87536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86310 q = 0) : d87537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86310, d87537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86310, d87537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86311 q = 0) : d87538 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86311, d87538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86311, d87538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86312 q = 0) : d87539 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86312, d87539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86312, d87539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5038 (p : Pattern) (selected : d86318 p = 0) : d87545 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86313 q = 0) : d87540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86313, d87540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5036 q selected
    | true =>
      simp only [d86313, d87540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5037 q selected
  have h2 (q : Pattern) (selected : d86314 q = 0) : d87541 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86314, d87541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86314, d87541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86315 q = 0) : d87542 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86315, d87542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86315, d87542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86316 q = 0) : d87543 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86316, d87543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86316, d87543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86317 q = 0) : d87544 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86317, d87544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86317, d87544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86318 q = 0) : d87545 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86318, d87545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86318, d87545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5039 (p : Pattern) (selected : d86321 p = 0) : d87548 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86299 q = 0) : d87526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86299, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5034 q selected
    | true =>
      simp only [d86299, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86300 q = 0) : d87527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86300, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86300, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86303 q = 0) : d87530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5035 q selected
    | true =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86304 q = 0) : d87531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86305 q = 0) : d87532 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86305, d87532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86305, d87532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86306 q = 0) : d87533 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86306, d87533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86306, d87533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86307 q = 0) : d87534 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86307, d87534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86307, d87534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86321 q = 0) : d87548 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86321, d87548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86321, d87548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5040 (p : Pattern) (selected : d86322 p = 0) : d87549 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86303 q = 0) : d87530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5035 q selected
    | true =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86304 q = 0) : d87531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86309 q = 0) : d87536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86309, d87536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86309, d87536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86310 q = 0) : d87537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86310, d87537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86310, d87537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86311 q = 0) : d87538 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86311, d87538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86311, d87538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86322 q = 0) : d87549 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86322, d87549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86322, d87549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5041 (p : Pattern) (selected : d86328 p = 0) : d87555 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86313 q = 0) : d87540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86313, d87540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5036 q selected
    | true =>
      simp only [d86313, d87540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5037 q selected
  have h2 (q : Pattern) (selected : d86314 q = 0) : d87541 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86314, d87541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86314, d87541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86315 q = 0) : d87542 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86315, d87542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86315, d87542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86316 q = 0) : d87543 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86316, d87543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86316, d87543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86317 q = 0) : d87544 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86317, d87544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86317, d87544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86323 q = 0) : d87550 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86323, d87550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5039 q selected
    | true =>
      simp only [d86323, d87550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5040 q selected
  have h7 (q : Pattern) (selected : d86324 q = 0) : d87551 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86324, d87551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86324, d87551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86325 q = 0) : d87552 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86325, d87552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86325, d87552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d86326 q = 0) : d87553 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86326, d87553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86326, d87553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86327 q = 0) : d87554 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86327, d87554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86327, d87554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86328 q = 0) : d87555 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86328, d87555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86328, d87555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5042 (p : Pattern) (selected : d86333 p = 0) : d87560 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86299 q = 0) : d87526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86299, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5034 q selected
    | true =>
      simp only [d86299, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86300 q = 0) : d87527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86300, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86300, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86303 q = 0) : d87530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5035 q selected
    | true =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86304 q = 0) : d87531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86305 q = 0) : d87532 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86305, d87532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86305, d87532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86306 q = 0) : d87533 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86306, d87533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86306, d87533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86332 q = 0) : d87559 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86332, d87559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86332, d87559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86333 q = 0) : d87560 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86333, d87560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86333, d87560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5043 (p : Pattern) (selected : d86335 p = 0) : d87562 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86303 q = 0) : d87530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5035 q selected
    | true =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86304 q = 0) : d87531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86309 q = 0) : d87536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86309, d87536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86309, d87536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86310 q = 0) : d87537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86310, d87537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86310, d87537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86334 q = 0) : d87561 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86334, d87561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86334, d87561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86335 q = 0) : d87562 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86335, d87562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86335, d87562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5044 (p : Pattern) (selected : d86342 p = 0) : d87569 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86299 q = 0) : d87526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86299, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5034 q selected
    | true =>
      simp only [d86299, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86300 q = 0) : d87527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86300, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86300, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86303 q = 0) : d87530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5035 q selected
    | true =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86304 q = 0) : d87531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86305 q = 0) : d87532 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86305, d87532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86305, d87532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86340 q = 0) : d87567 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86340, d87567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86340, d87567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86341 q = 0) : d87568 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86341, d87568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86341, d87568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86342 q = 0) : d87569 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86342, d87569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86342, d87569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5045 (p : Pattern) (selected : d86345 p = 0) : d87572 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86303 q = 0) : d87530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5035 q selected
    | true =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86304 q = 0) : d87531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86309 q = 0) : d87536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86309, d87536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86309, d87536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86343 q = 0) : d87570 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86343, d87570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86343, d87570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86344 q = 0) : d87571 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86344, d87571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86344, d87571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86345 q = 0) : d87572 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86345, d87572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86345, d87572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5046 (p : Pattern) (selected : d86352 p = 0) : d87579 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86349 q = 0) : d87576 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86349, d87576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86349, d87576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro389 q selected
  have h2 (q : Pattern) (selected : d86350 q = 0) : d87577 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86350, d87577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86350, d87577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86293 q = 0) : d87520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86293, d87520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86293, d87520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro390 q selected
  have h4 (q : Pattern) (selected : d86294 q = 0) : d87521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86294, d87521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86294, d87521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86351 q = 0) : d87578 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86351, d87578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86351, d87578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86352 q = 0) : d87579 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86352, d87579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86352, d87579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5047 (p : Pattern) (selected : d86358 p = 0) : d87585 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86353 q = 0) : d87580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86353, d87580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5046 q selected
    | true =>
      simp only [d86353, d87580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86354 q = 0) : d87581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86354, d87581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86354, d87581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86299 q = 0) : d87526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86299, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5034 q selected
    | true =>
      simp only [d86299, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86300 q = 0) : d87527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86300, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86300, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86355 q = 0) : d87582 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86355, d87582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86355, d87582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86356 q = 0) : d87583 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86356, d87583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86356, d87583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86357 q = 0) : d87584 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86357, d87584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86357, d87584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86358 q = 0) : d87585 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86358, d87585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86358, d87585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5048 (p : Pattern) (selected : d86365 p = 0) : d87525 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86360 q = 0) : d87520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86360, d87520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86360, d87520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro419 q selected
  have h2 (q : Pattern) (selected : d86361 q = 0) : d87521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86361, d87521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86361, d87521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86362 q = 0) : d87522 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86362, d87522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86362, d87522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro421 q selected
  have h4 (q : Pattern) (selected : d86363 q = 0) : d87523 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86363, d87523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86363, d87523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86364 q = 0) : d87524 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86364, d87524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86364, d87524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86365 q = 0) : d87525 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86365, d87525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86365, d87525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5049 (p : Pattern) (selected : d86369 p = 0) : d87529 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86362 q = 0) : d87522 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86362, d87522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86362, d87522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro421 q selected
  have h2 (q : Pattern) (selected : d86363 q = 0) : d87523 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86363, d87523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86363, d87523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86368 q = 0) : d87528 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86368, d87528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86368, d87528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86369 q = 0) : d87529 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86369, d87529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86369, d87529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5050 (p : Pattern) (selected : d86375 p = 0) : d87535 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86366 q = 0) : d87526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86366, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5048 q selected
    | true =>
      simp only [d86366, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86367 q = 0) : d87527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86367, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86367, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86370 q = 0) : d87530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86370, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5049 q selected
    | true =>
      simp only [d86370, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86371 q = 0) : d87531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86371, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86371, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86372 q = 0) : d87532 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86372, d87532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86372, d87532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86373 q = 0) : d87533 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86373, d87533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86373, d87533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86374 q = 0) : d87534 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86374, d87534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86374, d87534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86375 q = 0) : d87535 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86375, d87535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86375, d87535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5051 (p : Pattern) (selected : d86379 p = 0) : d87539 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86370 q = 0) : d87530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86370, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5049 q selected
    | true =>
      simp only [d86370, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86371 q = 0) : d87531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86371, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86371, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86376 q = 0) : d87536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86376, d87536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86376, d87536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86377 q = 0) : d87537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86377, d87537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86377, d87537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86378 q = 0) : d87538 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86378, d87538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86378, d87538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86379 q = 0) : d87539 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86379, d87539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86379, d87539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5052 (p : Pattern) (selected : d86385 p = 0) : d87591 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86299 q = 0) : d87526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86299, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5034 q selected
    | true =>
      simp only [d86299, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86300 q = 0) : d87527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86300, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86300, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86382 q = 0) : d87588 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86382, d87588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86382, d87588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86383 q = 0) : d87589 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86383, d87589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86383, d87589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86384 q = 0) : d87590 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86384, d87590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86384, d87590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86385 q = 0) : d87591 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86385, d87591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86385, d87591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5053 (p : Pattern) (selected : d86391 p = 0) : d87597 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86336 q = 0) : d87563 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86336, d87563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5042 q selected
    | true =>
      simp only [d86336, d87563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5043 q selected
  have h2 (q : Pattern) (selected : d86337 q = 0) : d87564 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86337, d87564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86337, d87564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86338 q = 0) : d87565 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86338, d87565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86338, d87565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86339 q = 0) : d87566 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86339, d87566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86339, d87566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86346 q = 0) : d87573 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86346, d87573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5044 q selected
    | true =>
      simp only [d86346, d87573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5045 q selected
  have h6 (q : Pattern) (selected : d86347 q = 0) : d87574 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86347, d87574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86347, d87574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86348 q = 0) : d87575 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86348, d87575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86348, d87575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86359 q = 0) : d87586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86359, d87586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5047 q selected
    | true =>
      simp only [d86359, d87586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5036 q selected
  have h9 (q : Pattern) (selected : d86380 q = 0) : d87540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86380, d87540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5050 q selected
    | true =>
      simp only [d86380, d87540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5051 q selected
  have h10 (q : Pattern) (selected : d86381 q = 0) : d87587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86381, d87587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d86381, d87587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86386 q = 0) : d87592 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86386, d87592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5052 q selected
    | true =>
      simp only [d86386, d87592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d86387 q = 0) : d87593 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86387, d87593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d86387, d87593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d86388 q = 0) : d87594 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86388, d87594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86388, d87594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d86389 q = 0) : d87595 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86389, d87595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86389, d87595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d86390 q = 0) : d87596 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86390, d87596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86390, d87596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d86391 q = 0) : d87597 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86391, d87597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86391, d87597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro5054 (p : Pattern) (selected : d86392 p = 0) : d87598 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86299 q = 0) : d87526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86299, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5034 q selected
    | true =>
      simp only [d86299, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86300 q = 0) : d87527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86300, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86300, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86303 q = 0) : d87530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5035 q selected
    | true =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86304 q = 0) : d87531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86305 q = 0) : d87532 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86305, d87532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86305, d87532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86306 q = 0) : d87533 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86306, d87533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86306, d87533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86332 q = 0) : d87559 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86332, d87559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86332, d87559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86392 q = 0) : d87598 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86392, d87598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86392, d87598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5055 (p : Pattern) (selected : d86393 p = 0) : d87599 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86303 q = 0) : d87530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5035 q selected
    | true =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86304 q = 0) : d87531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86309 q = 0) : d87536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86309, d87536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86309, d87536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86310 q = 0) : d87537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86310, d87537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86310, d87537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86334 q = 0) : d87561 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86334, d87561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86334, d87561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86393 q = 0) : d87599 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86393, d87599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86393, d87599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5056 (p : Pattern) (selected : d86398 p = 0) : d87604 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86299 q = 0) : d87526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86299, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5034 q selected
    | true =>
      simp only [d86299, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86300 q = 0) : d87527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86300, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86300, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86303 q = 0) : d87530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5035 q selected
    | true =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86304 q = 0) : d87531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86305 q = 0) : d87532 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86305, d87532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86305, d87532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86340 q = 0) : d87567 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86340, d87567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86340, d87567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86341 q = 0) : d87568 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86341, d87568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86341, d87568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86398 q = 0) : d87604 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86398, d87604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86398, d87604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5057 (p : Pattern) (selected : d86399 p = 0) : d87605 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86303 q = 0) : d87530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5035 q selected
    | true =>
      simp only [d86303, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86304 q = 0) : d87531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86304, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86309 q = 0) : d87536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86309, d87536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86309, d87536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86343 q = 0) : d87570 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86343, d87570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86343, d87570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86344 q = 0) : d87571 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86344, d87571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86344, d87571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86399 q = 0) : d87605 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86399, d87605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86399, d87605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5058 (p : Pattern) (selected : d86403 p = 0) : d87609 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86353 q = 0) : d87580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86353, d87580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5046 q selected
    | true =>
      simp only [d86353, d87580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86354 q = 0) : d87581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86354, d87581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86354, d87581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86299 q = 0) : d87526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86299, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5034 q selected
    | true =>
      simp only [d86299, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86300 q = 0) : d87527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86300, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86300, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86355 q = 0) : d87582 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86355, d87582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86355, d87582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86356 q = 0) : d87583 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86356, d87583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86356, d87583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86357 q = 0) : d87584 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86357, d87584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86357, d87584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86403 q = 0) : d87609 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86403, d87609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86403, d87609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5059 (p : Pattern) (selected : d86405 p = 0) : d87548 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86366 q = 0) : d87526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86366, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5048 q selected
    | true =>
      simp only [d86366, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86367 q = 0) : d87527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86367, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86367, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86370 q = 0) : d87530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86370, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5049 q selected
    | true =>
      simp only [d86370, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86371 q = 0) : d87531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86371, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86371, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86372 q = 0) : d87532 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86372, d87532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86372, d87532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86373 q = 0) : d87533 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86373, d87533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86373, d87533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86374 q = 0) : d87534 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86374, d87534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86374, d87534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86405 q = 0) : d87548 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86405, d87548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86405, d87548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5060 (p : Pattern) (selected : d86406 p = 0) : d87549 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86370 q = 0) : d87530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86370, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5049 q selected
    | true =>
      simp only [d86370, d87530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86371 q = 0) : d87531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86371, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86371, d87531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86376 q = 0) : d87536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86376, d87536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86376, d87536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86377 q = 0) : d87537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86377, d87537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86377, d87537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86378 q = 0) : d87538 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86378, d87538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86378, d87538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86406 q = 0) : d87549 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86406, d87549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86406, d87549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5061 (p : Pattern) (selected : d86409 p = 0) : d87612 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86299 q = 0) : d87526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86299, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5034 q selected
    | true =>
      simp only [d86299, d87526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86300 q = 0) : d87527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86300, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86300, d87527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86382 q = 0) : d87588 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86382, d87588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86382, d87588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86383 q = 0) : d87589 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86383, d87589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86383, d87589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86384 q = 0) : d87590 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86384, d87590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86384, d87590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86409 q = 0) : d87612 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86409, d87612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86409, d87612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5062 (p : Pattern) (selected : d86415 p = 0) : d87618 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86336 q = 0) : d87563 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86336, d87563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5042 q selected
    | true =>
      simp only [d86336, d87563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5043 q selected
  have h2 (q : Pattern) (selected : d86337 q = 0) : d87564 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86337, d87564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86337, d87564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86338 q = 0) : d87565 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86338, d87565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86338, d87565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86339 q = 0) : d87566 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86339, d87566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86339, d87566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86346 q = 0) : d87573 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86346, d87573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5044 q selected
    | true =>
      simp only [d86346, d87573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5045 q selected
  have h6 (q : Pattern) (selected : d86347 q = 0) : d87574 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86347, d87574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86347, d87574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86348 q = 0) : d87575 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86348, d87575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86348, d87575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86359 q = 0) : d87586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86359, d87586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5047 q selected
    | true =>
      simp only [d86359, d87586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5036 q selected
  have h9 (q : Pattern) (selected : d86380 q = 0) : d87540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86380, d87540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5050 q selected
    | true =>
      simp only [d86380, d87540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5051 q selected
  have h10 (q : Pattern) (selected : d86381 q = 0) : d87587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86381, d87587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d86381, d87587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86386 q = 0) : d87592 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86386, d87592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5052 q selected
    | true =>
      simp only [d86386, d87592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d86387 q = 0) : d87593 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86387, d87593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d86387, d87593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d86388 q = 0) : d87594 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86388, d87594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86388, d87594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d86389 q = 0) : d87595 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86389, d87595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86389, d87595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d86390 q = 0) : d87596 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86390, d87596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86390, d87596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d86394 q = 0) : d87600 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86394, d87600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5054 q selected
    | true =>
      simp only [d86394, d87600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5055 q selected
  have h17 (q : Pattern) (selected : d86395 q = 0) : d87601 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86395, d87601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86395, d87601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d86396 q = 0) : d87602 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86396, d87602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d86396, d87602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d86397 q = 0) : d87603 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86397, d87603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86397, d87603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d86400 q = 0) : d87606 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86400, d87606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5056 q selected
    | true =>
      simp only [d86400, d87606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5057 q selected
  have h21 (q : Pattern) (selected : d86401 q = 0) : d87607 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86401, d87607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86401, d87607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d86402 q = 0) : d87608 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86402, d87608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d86402, d87608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d86404 q = 0) : d87610 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86404, d87610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5058 q selected
    | true =>
      simp only [d86404, d87610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5039 q selected
  have h24 (q : Pattern) (selected : d86407 q = 0) : d87550 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86407, d87550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5059 q selected
    | true =>
      simp only [d86407, d87550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5060 q selected
  have h25 (q : Pattern) (selected : d86408 q = 0) : d87611 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86408, d87611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d86408, d87611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d86410 q = 0) : d87613 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86410, d87613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5061 q selected
    | true =>
      simp only [d86410, d87613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d86411 q = 0) : d87614 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86411, d87614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d86411, d87614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d86412 q = 0) : d87615 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86412, d87615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d86412, d87615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d86413 q = 0) : d87616 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86413, d87616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d86413, d87616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d86414 q = 0) : d87617 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86414, d87617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d86414, d87617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d86415 q = 0) : d87618 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86415, d87618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d86415, d87618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro5063 (p : Pattern) (selected : d86422 p = 0) : d87625 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86313 q = 0) : d87540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86313, d87540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5036 q selected
    | true =>
      simp only [d86313, d87540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5037 q selected
  have h2 (q : Pattern) (selected : d86314 q = 0) : d87541 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86314, d87541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86314, d87541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86315 q = 0) : d87542 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86315, d87542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86315, d87542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86316 q = 0) : d87543 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86316, d87543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86316, d87543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86317 q = 0) : d87544 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86317, d87544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86317, d87544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86417 q = 0) : d87620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86417, d87620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5037 q selected
    | true =>
      simp only [d86417, d87620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86418 q = 0) : d87621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86418, d87621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86418, d87621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86419 q = 0) : d87622 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86419, d87622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86419, d87622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d86420 q = 0) : d87623 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86420, d87623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86420, d87623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86421 q = 0) : d87624 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86421, d87624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86421, d87624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86422 q = 0) : d87625 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86422, d87625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86422, d87625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5064 (p : Pattern) (selected : d86428 p = 0) : d87631 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86417 q = 0) : d87620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86417, d87620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5037 q selected
    | true =>
      simp only [d86417, d87620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86418 q = 0) : d87621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86418, d87621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86418, d87621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86419 q = 0) : d87622 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86419, d87622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86419, d87622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86420 q = 0) : d87623 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86420, d87623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86420, d87623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86421 q = 0) : d87624 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86421, d87624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86421, d87624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86423 q = 0) : d87626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86423, d87626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5040 q selected
    | true =>
      simp only [d86423, d87626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86424 q = 0) : d87627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86424, d87627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86424, d87627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86425 q = 0) : d87628 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86425, d87628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86425, d87628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d86426 q = 0) : d87629 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86426, d87629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86426, d87629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86427 q = 0) : d87630 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86427, d87630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86427, d87630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86428 q = 0) : d87631 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86428, d87631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86428, d87631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5065 (p : Pattern) (selected : d86435 p = 0) : d87638 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86404 q = 0) : d87610 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86404, d87610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5058 q selected
    | true =>
      simp only [d86404, d87610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5039 q selected
  have h2 (q : Pattern) (selected : d86407 q = 0) : d87550 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86407, d87550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5059 q selected
    | true =>
      simp only [d86407, d87550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5060 q selected
  have h3 (q : Pattern) (selected : d86408 q = 0) : d87611 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86408, d87611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86408, d87611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86410 q = 0) : d87613 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86410, d87613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5061 q selected
    | true =>
      simp only [d86410, d87613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86411 q = 0) : d87614 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86411, d87614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86411, d87614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86412 q = 0) : d87615 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86412, d87615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86412, d87615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86433 q = 0) : d87636 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86433, d87636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86433, d87636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86434 q = 0) : d87637 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86434, d87637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86434, d87637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86435 q = 0) : d87638 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86435, d87638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86435, d87638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro5066 (p : Pattern) (selected : d86437 p = 0) : d87640 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86423 q = 0) : d87626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86423, d87626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5040 q selected
    | true =>
      simp only [d86423, d87626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86424 q = 0) : d87627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86424, d87627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86424, d87627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86425 q = 0) : d87628 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86425, d87628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86425, d87628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86426 q = 0) : d87629 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86426, d87629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86426, d87629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86427 q = 0) : d87630 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86427, d87630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86427, d87630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86437 q = 0) : d87640 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86437, d87640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86437, d87640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5067 (p : Pattern) (selected : d86448 p = 0) : d87651 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86443 q = 0) : d87646 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86443, d87646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86443, d87646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro440 q selected
  have h2 (q : Pattern) (selected : d86444 q = 0) : d87647 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86444, d87647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86444, d87647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86445 q = 0) : d87648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86445, d87648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86445, d87648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro441 q selected
  have h4 (q : Pattern) (selected : d86446 q = 0) : d87649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86446, d87649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86446, d87649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86447 q = 0) : d87650 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86447, d87650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86447, d87650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86448 q = 0) : d87651 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86448, d87651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86448, d87651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5068 (p : Pattern) (selected : d86454 p = 0) : d87657 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86445 q = 0) : d87648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86445, d87648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86445, d87648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro441 q selected
  have h2 (q : Pattern) (selected : d86446 q = 0) : d87649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86446, d87649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86446, d87649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86451 q = 0) : d87654 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86451, d87654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86451, d87654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro442 q selected
  have h4 (q : Pattern) (selected : d86452 q = 0) : d87655 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86452, d87655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86452, d87655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86453 q = 0) : d87656 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86453, d87656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86453, d87656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86454 q = 0) : d87657 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86454, d87657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86454, d87657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5069 (p : Pattern) (selected : d86460 p = 0) : d87663 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86449 q = 0) : d87652 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86449, d87652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5067 q selected
    | true =>
      simp only [d86449, d87652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86450 q = 0) : d87653 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86450, d87653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86450, d87653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86455 q = 0) : d87658 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86455, d87658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5068 q selected
    | true =>
      simp only [d86455, d87658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86456 q = 0) : d87659 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86456, d87659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86456, d87659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86457 q = 0) : d87660 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86457, d87660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86457, d87660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86458 q = 0) : d87661 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86458, d87661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86458, d87661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86459 q = 0) : d87662 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86459, d87662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86459, d87662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86460 q = 0) : d87663 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86460, d87663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86460, d87663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5070 (p : Pattern) (selected : d86462 p = 0) : d87665 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86451 q = 0) : d87654 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86451, d87654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86451, d87654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro442 q selected
  have h2 (q : Pattern) (selected : d86452 q = 0) : d87655 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86452, d87655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86452, d87655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86461 q = 0) : d87664 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86461, d87664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86461, d87664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86462 q = 0) : d87665 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86462, d87665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86462, d87665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5071 (p : Pattern) (selected : d86468 p = 0) : d87671 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86455 q = 0) : d87658 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86455, d87658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5068 q selected
    | true =>
      simp only [d86455, d87658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86456 q = 0) : d87659 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86456, d87659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86456, d87659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86463 q = 0) : d87666 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86463, d87666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5070 q selected
    | true =>
      simp only [d86463, d87666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86464 q = 0) : d87667 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86464, d87667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86464, d87667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86465 q = 0) : d87668 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86465, d87668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86465, d87668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86466 q = 0) : d87669 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86466, d87669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86466, d87669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86467 q = 0) : d87670 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86467, d87670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86467, d87670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86468 q = 0) : d87671 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86468, d87671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86468, d87671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5072 (p : Pattern) (selected : d86475 p = 0) : d87657 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86470 q = 0) : d87648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86470, d87648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86470, d87648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro449 q selected
  have h2 (q : Pattern) (selected : d86471 q = 0) : d87649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86471, d87649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86471, d87649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86472 q = 0) : d87654 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86472, d87654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86472, d87654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro450 q selected
  have h4 (q : Pattern) (selected : d86473 q = 0) : d87655 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86473, d87655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86473, d87655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86474 q = 0) : d87656 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86474, d87656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86474, d87656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86475 q = 0) : d87657 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86475, d87657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86475, d87657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5073 (p : Pattern) (selected : d86479 p = 0) : d87665 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86472 q = 0) : d87654 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86472, d87654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86472, d87654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro450 q selected
  have h2 (q : Pattern) (selected : d86473 q = 0) : d87655 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86473, d87655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86473, d87655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86478 q = 0) : d87664 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86478, d87664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86478, d87664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86479 q = 0) : d87665 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86479, d87665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86479, d87665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5074 (p : Pattern) (selected : d86485 p = 0) : d87671 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86476 q = 0) : d87658 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86476, d87658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5072 q selected
    | true =>
      simp only [d86476, d87658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86477 q = 0) : d87659 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86477, d87659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86477, d87659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86480 q = 0) : d87666 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86480, d87666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5073 q selected
    | true =>
      simp only [d86480, d87666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86481 q = 0) : d87667 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86481, d87667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86481, d87667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86482 q = 0) : d87668 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86482, d87668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86482, d87668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86483 q = 0) : d87669 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86483, d87669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86483, d87669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86484 q = 0) : d87670 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86484, d87670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86484, d87670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86485 q = 0) : d87671 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86485, d87671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86485, d87671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5075 (p : Pattern) (selected : d86489 p = 0) : d87676 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86480 q = 0) : d87666 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86480, d87666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5073 q selected
    | true =>
      simp only [d86480, d87666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86481 q = 0) : d87667 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86481, d87667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86481, d87667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86486 q = 0) : d87673 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86486, d87673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86486, d87673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86487 q = 0) : d87674 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86487, d87674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86487, d87674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86488 q = 0) : d87675 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86488, d87675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86488, d87675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86489 q = 0) : d87676 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86489, d87676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86489, d87676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5076 (p : Pattern) (selected : d86495 p = 0) : d87682 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86455 q = 0) : d87658 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86455, d87658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5068 q selected
    | true =>
      simp only [d86455, d87658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86456 q = 0) : d87659 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86456, d87659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86456, d87659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86492 q = 0) : d87679 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86492, d87679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86492, d87679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86493 q = 0) : d87680 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86493, d87680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86493, d87680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86494 q = 0) : d87681 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86494, d87681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86494, d87681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86495 q = 0) : d87682 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86495, d87682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86495, d87682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5077 (p : Pattern) (selected : d86501 p = 0) : d87688 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86469 q = 0) : d87672 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86469, d87672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5069 q selected
    | true =>
      simp only [d86469, d87672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5071 q selected
  have h2 (q : Pattern) (selected : d86490 q = 0) : d87677 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86490, d87677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5074 q selected
    | true =>
      simp only [d86490, d87677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5075 q selected
  have h3 (q : Pattern) (selected : d86491 q = 0) : d87678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86491, d87678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86491, d87678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86496 q = 0) : d87683 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86496, d87683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5076 q selected
    | true =>
      simp only [d86496, d87683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86497 q = 0) : d87684 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86497, d87684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86497, d87684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86498 q = 0) : d87685 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86498, d87685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86498, d87685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86499 q = 0) : d87686 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86499, d87686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86499, d87686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86500 q = 0) : d87687 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86500, d87687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86500, d87687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86501 q = 0) : d87688 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86501, d87688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86501, d87688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro5078 (p : Pattern) (selected : d86506 p = 0) : d87676 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86463 q = 0) : d87666 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86463, d87666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5070 q selected
    | true =>
      simp only [d86463, d87666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86464 q = 0) : d87667 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86464, d87667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86464, d87667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86503 q = 0) : d87673 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86503, d87673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86503, d87673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86504 q = 0) : d87674 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86504, d87674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86504, d87674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86505 q = 0) : d87675 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86505, d87675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86505, d87675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86506 q = 0) : d87676 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86506, d87676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86506, d87676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5079 (p : Pattern) (selected : d86512 p = 0) : d87695 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86507 q = 0) : d87690 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86507, d87690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5078 q selected
    | true =>
      simp only [d86507, d87690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86508 q = 0) : d87691 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86508, d87691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86508, d87691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86509 q = 0) : d87692 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86509, d87692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86509, d87692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86510 q = 0) : d87693 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86510, d87693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86510, d87693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86511 q = 0) : d87694 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86511, d87694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86511, d87694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86512 q = 0) : d87695 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86512, d87695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86512, d87695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5080 (p : Pattern) (selected : d86518 p = 0) : d87701 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86319 q = 0) : d87546 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86319, d87546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86319, d87546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5038 q selected
  have h2 (q : Pattern) (selected : d86320 q = 0) : d87547 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86320, d87547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86320, d87547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d86329 q = 0) : d87556 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86329, d87556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5038 q selected
    | true =>
      simp only [d86329, d87556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5041 q selected
  have h4 (q : Pattern) (selected : d86330 q = 0) : d87557 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86330, d87557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86330, d87557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86331 q = 0) : d87558 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86331, d87558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86331, d87558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86416 q = 0) : d87619 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86416, d87619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5053 q selected
    | true =>
      simp only [d86416, d87619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5062 q selected
  have h7 (q : Pattern) (selected : d86429 q = 0) : d87632 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86429, d87632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5063 q selected
    | true =>
      simp only [d86429, d87632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5064 q selected
  have h8 (q : Pattern) (selected : d86430 q = 0) : d87633 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86430, d87633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86430, d87633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86431 q = 0) : d87634 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86431, d87634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d86431, d87634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d86432 q = 0) : d87635 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86432, d87635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86432, d87635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86436 q = 0) : d87639 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86436, d87639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86436, d87639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5065 q selected
  have h12 (q : Pattern) (selected : d86438 q = 0) : d87641 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86438, d87641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86438, d87641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5066 q selected
  have h13 (q : Pattern) (selected : d86439 q = 0) : d87642 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86439, d87642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d86439, d87642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d86440 q = 0) : d87643 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86440, d87643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d86440, d87643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d86441 q = 0) : d87644 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86441, d87644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d86441, d87644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d86442 q = 0) : d87645 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d86442, d87645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86442, d87645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d86502 q = 0) : d87689 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86502, d87689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86502, d87689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5077 q selected
  have h18 (q : Pattern) (selected : d86513 q = 0) : d87696 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86513, d87696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86513, d87696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5079 q selected
  have h19 (q : Pattern) (selected : d86514 q = 0) : d87697 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86514, d87697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d86514, d87697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d86515 q = 0) : d87698 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86515, d87698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d86515, d87698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d86516 q = 0) : d87699 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86516, d87699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d86516, d87699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d86517 q = 0) : d87700 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d86517, d87700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d86517, d87700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d86518 q = 0) : d87701 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d86518, d87701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d86518, d87701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro5081 (p : Pattern) (selected : d86524 p = 0) : d87707 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86519 q = 0) : d87702 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d86519, d87702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86519, d87702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5080 q selected
  have h2 (q : Pattern) (selected : d86520 q = 0) : d87703 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d86520, d87703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86520, d87703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86521 q = 0) : d87704 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d86521, d87704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86521, d87704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86522 q = 0) : d87705 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d86522, d87705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86522, d87705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86523 q = 0) : d87706 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d86523, d87706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86523, d87706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86524 q = 0) : d87707 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d86524, d87707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86524, d87707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5082 (p : Pattern) (selected : d86533 p = 0) : d87716 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86528 q = 0) : d87711 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86528, d87711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86528, d87711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro472 q selected
  have h2 (q : Pattern) (selected : d86529 q = 0) : d87712 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86529, d87712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86529, d87712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86530 q = 0) : d87713 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86530, d87713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86530, d87713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro474 q selected
  have h4 (q : Pattern) (selected : d86531 q = 0) : d87714 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86531, d87714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86531, d87714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86532 q = 0) : d87715 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86532, d87715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86532, d87715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86533 q = 0) : d87716 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86533, d87716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86533, d87716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5083 (p : Pattern) (selected : d86537 p = 0) : d87720 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86530 q = 0) : d87713 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86530, d87713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86530, d87713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro474 q selected
  have h2 (q : Pattern) (selected : d86531 q = 0) : d87714 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86531, d87714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86531, d87714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86536 q = 0) : d87719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86536, d87719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86536, d87719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86537 q = 0) : d87720 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86537, d87720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86537, d87720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5084 (p : Pattern) (selected : d86543 p = 0) : d87726 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86534 q = 0) : d87717 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86534, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5082 q selected
    | true =>
      simp only [d86534, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86535 q = 0) : d87718 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86535, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86535, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86538 q = 0) : d87721 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5083 q selected
    | true =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86539 q = 0) : d87722 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86540 q = 0) : d87723 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86540, d87723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86540, d87723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86541 q = 0) : d87724 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86541, d87724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86541, d87724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86542 q = 0) : d87725 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86542, d87725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86542, d87725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86543 q = 0) : d87726 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86543, d87726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86543, d87726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5085 (p : Pattern) (selected : d86547 p = 0) : d87730 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86538 q = 0) : d87721 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5083 q selected
    | true =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86539 q = 0) : d87722 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86544 q = 0) : d87727 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86544, d87727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86544, d87727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86545 q = 0) : d87728 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86545, d87728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86545, d87728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86546 q = 0) : d87729 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86546, d87729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86546, d87729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86547 q = 0) : d87730 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86547, d87730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86547, d87730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5086 (p : Pattern) (selected : d86553 p = 0) : d87736 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86548 q = 0) : d87731 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86548, d87731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5084 q selected
    | true =>
      simp only [d86548, d87731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5085 q selected
  have h2 (q : Pattern) (selected : d86549 q = 0) : d87732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86549, d87732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86549, d87732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86550 q = 0) : d87733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86550, d87733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86550, d87733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86551 q = 0) : d87734 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86551, d87734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86551, d87734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86552 q = 0) : d87735 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86552, d87735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86552, d87735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86553 q = 0) : d87736 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86553, d87736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86553, d87736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5087 (p : Pattern) (selected : d86556 p = 0) : d87739 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86534 q = 0) : d87717 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86534, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5082 q selected
    | true =>
      simp only [d86534, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86535 q = 0) : d87718 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86535, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86535, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86538 q = 0) : d87721 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5083 q selected
    | true =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86539 q = 0) : d87722 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86540 q = 0) : d87723 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86540, d87723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86540, d87723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86541 q = 0) : d87724 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86541, d87724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86541, d87724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86542 q = 0) : d87725 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86542, d87725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86542, d87725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86556 q = 0) : d87739 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86556, d87739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86556, d87739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5088 (p : Pattern) (selected : d86557 p = 0) : d87740 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86538 q = 0) : d87721 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5083 q selected
    | true =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86539 q = 0) : d87722 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86544 q = 0) : d87727 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86544, d87727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86544, d87727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86545 q = 0) : d87728 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86545, d87728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86545, d87728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86546 q = 0) : d87729 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86546, d87729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86546, d87729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86557 q = 0) : d87740 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86557, d87740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86557, d87740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5089 (p : Pattern) (selected : d86563 p = 0) : d87746 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86548 q = 0) : d87731 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86548, d87731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5084 q selected
    | true =>
      simp only [d86548, d87731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5085 q selected
  have h2 (q : Pattern) (selected : d86549 q = 0) : d87732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86549, d87732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86549, d87732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86550 q = 0) : d87733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86550, d87733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86550, d87733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86551 q = 0) : d87734 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86551, d87734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86551, d87734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86552 q = 0) : d87735 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86552, d87735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86552, d87735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86558 q = 0) : d87741 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86558, d87741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5087 q selected
    | true =>
      simp only [d86558, d87741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5088 q selected
  have h7 (q : Pattern) (selected : d86559 q = 0) : d87742 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86559, d87742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86559, d87742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86560 q = 0) : d87743 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86560, d87743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86560, d87743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d86561 q = 0) : d87744 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86561, d87744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86561, d87744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86562 q = 0) : d87745 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86562, d87745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86562, d87745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86563 q = 0) : d87746 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86563, d87746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86563, d87746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5090 (p : Pattern) (selected : d86568 p = 0) : d87751 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86534 q = 0) : d87717 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86534, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5082 q selected
    | true =>
      simp only [d86534, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86535 q = 0) : d87718 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86535, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86535, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86538 q = 0) : d87721 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5083 q selected
    | true =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86539 q = 0) : d87722 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86540 q = 0) : d87723 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86540, d87723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86540, d87723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86541 q = 0) : d87724 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86541, d87724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86541, d87724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86567 q = 0) : d87750 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86567, d87750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86567, d87750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86568 q = 0) : d87751 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86568, d87751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86568, d87751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5091 (p : Pattern) (selected : d86570 p = 0) : d87753 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86538 q = 0) : d87721 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5083 q selected
    | true =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86539 q = 0) : d87722 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86544 q = 0) : d87727 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86544, d87727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86544, d87727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86545 q = 0) : d87728 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86545, d87728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86545, d87728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86569 q = 0) : d87752 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86569, d87752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86569, d87752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86570 q = 0) : d87753 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86570, d87753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86570, d87753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5092 (p : Pattern) (selected : d86577 p = 0) : d87760 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86534 q = 0) : d87717 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86534, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5082 q selected
    | true =>
      simp only [d86534, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86535 q = 0) : d87718 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86535, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86535, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86538 q = 0) : d87721 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5083 q selected
    | true =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86539 q = 0) : d87722 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86540 q = 0) : d87723 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86540, d87723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86540, d87723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86575 q = 0) : d87758 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86575, d87758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86575, d87758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86576 q = 0) : d87759 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86576, d87759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86576, d87759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86577 q = 0) : d87760 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86577, d87760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86577, d87760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5093 (p : Pattern) (selected : d86580 p = 0) : d87763 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86538 q = 0) : d87721 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5083 q selected
    | true =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86539 q = 0) : d87722 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86544 q = 0) : d87727 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86544, d87727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86544, d87727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86578 q = 0) : d87761 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86578, d87761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86578, d87761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86579 q = 0) : d87762 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86579, d87762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86579, d87762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86580 q = 0) : d87763 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86580, d87763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86580, d87763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5094 (p : Pattern) (selected : d86587 p = 0) : d87770 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86584 q = 0) : d87767 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86584, d87767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86584, d87767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro471 q selected
  have h2 (q : Pattern) (selected : d86585 q = 0) : d87768 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86585, d87768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86585, d87768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86528 q = 0) : d87711 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86528, d87711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86528, d87711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro472 q selected
  have h4 (q : Pattern) (selected : d86529 q = 0) : d87712 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86529, d87712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86529, d87712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86586 q = 0) : d87769 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86586, d87769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86586, d87769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86587 q = 0) : d87770 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86587, d87770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86587, d87770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5095 (p : Pattern) (selected : d86593 p = 0) : d87776 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86588 q = 0) : d87771 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86588, d87771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5094 q selected
    | true =>
      simp only [d86588, d87771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86589 q = 0) : d87772 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86589, d87772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86589, d87772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86534 q = 0) : d87717 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86534, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5082 q selected
    | true =>
      simp only [d86534, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86535 q = 0) : d87718 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86535, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86535, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86590 q = 0) : d87773 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86590, d87773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86590, d87773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86591 q = 0) : d87774 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86591, d87774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86591, d87774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86592 q = 0) : d87775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86592, d87775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86592, d87775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86593 q = 0) : d87776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86593, d87776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86593, d87776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5096 (p : Pattern) (selected : d86600 p = 0) : d87716 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86595 q = 0) : d87711 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86595, d87711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86595, d87711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro505 q selected
  have h2 (q : Pattern) (selected : d86596 q = 0) : d87712 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86596, d87712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86596, d87712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86597 q = 0) : d87713 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86597, d87713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86597, d87713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro507 q selected
  have h4 (q : Pattern) (selected : d86598 q = 0) : d87714 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86598, d87714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86598, d87714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86599 q = 0) : d87715 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86599, d87715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86599, d87715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86600 q = 0) : d87716 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86600, d87716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86600, d87716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5097 (p : Pattern) (selected : d86604 p = 0) : d87720 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86597 q = 0) : d87713 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86597, d87713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86597, d87713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro507 q selected
  have h2 (q : Pattern) (selected : d86598 q = 0) : d87714 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86598, d87714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86598, d87714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86603 q = 0) : d87719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86603, d87719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86603, d87719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86604 q = 0) : d87720 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86604, d87720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86604, d87720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5098 (p : Pattern) (selected : d86610 p = 0) : d87726 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86601 q = 0) : d87717 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86601, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5096 q selected
    | true =>
      simp only [d86601, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86602 q = 0) : d87718 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86602, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86602, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86605 q = 0) : d87721 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86605, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5097 q selected
    | true =>
      simp only [d86605, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86606 q = 0) : d87722 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86606, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86606, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86607 q = 0) : d87723 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86607, d87723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86607, d87723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86608 q = 0) : d87724 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86608, d87724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86608, d87724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86609 q = 0) : d87725 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86609, d87725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86609, d87725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86610 q = 0) : d87726 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86610, d87726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86610, d87726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5099 (p : Pattern) (selected : d86614 p = 0) : d87730 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86605 q = 0) : d87721 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86605, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5097 q selected
    | true =>
      simp only [d86605, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86606 q = 0) : d87722 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86606, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86606, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86611 q = 0) : d87727 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86611, d87727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86611, d87727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86612 q = 0) : d87728 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86612, d87728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86612, d87728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86613 q = 0) : d87729 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86613, d87729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86613, d87729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86614 q = 0) : d87730 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86614, d87730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86614, d87730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5100 (p : Pattern) (selected : d86620 p = 0) : d87782 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86534 q = 0) : d87717 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86534, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5082 q selected
    | true =>
      simp only [d86534, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86535 q = 0) : d87718 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86535, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86535, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86617 q = 0) : d87779 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86617, d87779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86617, d87779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86618 q = 0) : d87780 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86618, d87780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86618, d87780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86619 q = 0) : d87781 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86619, d87781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86619, d87781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86620 q = 0) : d87782 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86620, d87782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86620, d87782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5101 (p : Pattern) (selected : d86626 p = 0) : d87788 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86571 q = 0) : d87754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86571, d87754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5090 q selected
    | true =>
      simp only [d86571, d87754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5091 q selected
  have h2 (q : Pattern) (selected : d86572 q = 0) : d87755 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86572, d87755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86572, d87755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86573 q = 0) : d87756 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86573, d87756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86573, d87756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86574 q = 0) : d87757 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86574, d87757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86574, d87757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86581 q = 0) : d87764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86581, d87764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5092 q selected
    | true =>
      simp only [d86581, d87764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5093 q selected
  have h6 (q : Pattern) (selected : d86582 q = 0) : d87765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86582, d87765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86582, d87765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86583 q = 0) : d87766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86583, d87766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86583, d87766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86594 q = 0) : d87777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86594, d87777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5095 q selected
    | true =>
      simp only [d86594, d87777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5084 q selected
  have h9 (q : Pattern) (selected : d86615 q = 0) : d87731 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86615, d87731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5098 q selected
    | true =>
      simp only [d86615, d87731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5099 q selected
  have h10 (q : Pattern) (selected : d86616 q = 0) : d87778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86616, d87778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d86616, d87778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86621 q = 0) : d87783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86621, d87783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5100 q selected
    | true =>
      simp only [d86621, d87783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d86622 q = 0) : d87784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86622, d87784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d86622, d87784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d86623 q = 0) : d87785 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86623, d87785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86623, d87785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d86624 q = 0) : d87786 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86624, d87786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86624, d87786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d86625 q = 0) : d87787 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86625, d87787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86625, d87787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d86626 q = 0) : d87788 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86626, d87788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86626, d87788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro5102 (p : Pattern) (selected : d86627 p = 0) : d87789 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86534 q = 0) : d87717 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86534, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5082 q selected
    | true =>
      simp only [d86534, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86535 q = 0) : d87718 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86535, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86535, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86538 q = 0) : d87721 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5083 q selected
    | true =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86539 q = 0) : d87722 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86540 q = 0) : d87723 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86540, d87723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86540, d87723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86541 q = 0) : d87724 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86541, d87724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86541, d87724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86567 q = 0) : d87750 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86567, d87750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86567, d87750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86627 q = 0) : d87789 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86627, d87789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86627, d87789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5103 (p : Pattern) (selected : d86628 p = 0) : d87790 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86538 q = 0) : d87721 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5083 q selected
    | true =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86539 q = 0) : d87722 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86544 q = 0) : d87727 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86544, d87727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86544, d87727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86545 q = 0) : d87728 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86545, d87728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86545, d87728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86569 q = 0) : d87752 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86569, d87752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86569, d87752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86628 q = 0) : d87790 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86628, d87790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86628, d87790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5104 (p : Pattern) (selected : d86633 p = 0) : d87795 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86534 q = 0) : d87717 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86534, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5082 q selected
    | true =>
      simp only [d86534, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86535 q = 0) : d87718 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86535, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86535, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86538 q = 0) : d87721 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5083 q selected
    | true =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86539 q = 0) : d87722 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86540 q = 0) : d87723 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86540, d87723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86540, d87723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86575 q = 0) : d87758 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86575, d87758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86575, d87758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86576 q = 0) : d87759 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86576, d87759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86576, d87759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86633 q = 0) : d87795 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86633, d87795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86633, d87795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5105 (p : Pattern) (selected : d86634 p = 0) : d87796 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86538 q = 0) : d87721 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5083 q selected
    | true =>
      simp only [d86538, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86539 q = 0) : d87722 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86539, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86544 q = 0) : d87727 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86544, d87727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86544, d87727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86578 q = 0) : d87761 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86578, d87761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86578, d87761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86579 q = 0) : d87762 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86579, d87762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86579, d87762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86634 q = 0) : d87796 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86634, d87796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86634, d87796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5106 (p : Pattern) (selected : d86638 p = 0) : d87800 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86588 q = 0) : d87771 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86588, d87771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5094 q selected
    | true =>
      simp only [d86588, d87771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86589 q = 0) : d87772 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86589, d87772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86589, d87772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86534 q = 0) : d87717 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86534, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5082 q selected
    | true =>
      simp only [d86534, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86535 q = 0) : d87718 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86535, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86535, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86590 q = 0) : d87773 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86590, d87773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86590, d87773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86591 q = 0) : d87774 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86591, d87774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86591, d87774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86592 q = 0) : d87775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86592, d87775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86592, d87775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86638 q = 0) : d87800 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86638, d87800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86638, d87800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5107 (p : Pattern) (selected : d86640 p = 0) : d87739 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86601 q = 0) : d87717 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86601, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5096 q selected
    | true =>
      simp only [d86601, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86602 q = 0) : d87718 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86602, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86602, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86605 q = 0) : d87721 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86605, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5097 q selected
    | true =>
      simp only [d86605, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86606 q = 0) : d87722 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86606, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86606, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86607 q = 0) : d87723 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86607, d87723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86607, d87723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86608 q = 0) : d87724 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86608, d87724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86608, d87724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86609 q = 0) : d87725 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86609, d87725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86609, d87725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86640 q = 0) : d87739 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86640, d87739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86640, d87739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5108 (p : Pattern) (selected : d86641 p = 0) : d87740 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86605 q = 0) : d87721 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86605, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5097 q selected
    | true =>
      simp only [d86605, d87721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86606 q = 0) : d87722 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86606, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86606, d87722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86611 q = 0) : d87727 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86611, d87727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86611, d87727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86612 q = 0) : d87728 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86612, d87728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86612, d87728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86613 q = 0) : d87729 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86613, d87729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86613, d87729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86641 q = 0) : d87740 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86641, d87740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86641, d87740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5109 (p : Pattern) (selected : d86644 p = 0) : d87803 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86534 q = 0) : d87717 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86534, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5082 q selected
    | true =>
      simp only [d86534, d87717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86535 q = 0) : d87718 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86535, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86535, d87718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86617 q = 0) : d87779 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86617, d87779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86617, d87779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86618 q = 0) : d87780 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86618, d87780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86618, d87780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86619 q = 0) : d87781 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86619, d87781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86619, d87781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86644 q = 0) : d87803 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86644, d87803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86644, d87803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5110 (p : Pattern) (selected : d86650 p = 0) : d87809 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86571 q = 0) : d87754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86571, d87754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5090 q selected
    | true =>
      simp only [d86571, d87754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5091 q selected
  have h2 (q : Pattern) (selected : d86572 q = 0) : d87755 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86572, d87755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86572, d87755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86573 q = 0) : d87756 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86573, d87756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86573, d87756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86574 q = 0) : d87757 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86574, d87757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86574, d87757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86581 q = 0) : d87764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86581, d87764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5092 q selected
    | true =>
      simp only [d86581, d87764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5093 q selected
  have h6 (q : Pattern) (selected : d86582 q = 0) : d87765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86582, d87765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86582, d87765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86583 q = 0) : d87766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86583, d87766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86583, d87766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86594 q = 0) : d87777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86594, d87777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5095 q selected
    | true =>
      simp only [d86594, d87777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5084 q selected
  have h9 (q : Pattern) (selected : d86615 q = 0) : d87731 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86615, d87731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5098 q selected
    | true =>
      simp only [d86615, d87731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5099 q selected
  have h10 (q : Pattern) (selected : d86616 q = 0) : d87778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86616, d87778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d86616, d87778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86621 q = 0) : d87783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86621, d87783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5100 q selected
    | true =>
      simp only [d86621, d87783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d86622 q = 0) : d87784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86622, d87784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d86622, d87784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d86623 q = 0) : d87785 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86623, d87785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86623, d87785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d86624 q = 0) : d87786 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86624, d87786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86624, d87786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d86625 q = 0) : d87787 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86625, d87787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86625, d87787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d86629 q = 0) : d87791 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86629, d87791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5102 q selected
    | true =>
      simp only [d86629, d87791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5103 q selected
  have h17 (q : Pattern) (selected : d86630 q = 0) : d87792 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86630, d87792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86630, d87792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d86631 q = 0) : d87793 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86631, d87793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d86631, d87793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d86632 q = 0) : d87794 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86632, d87794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86632, d87794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d86635 q = 0) : d87797 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86635, d87797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5104 q selected
    | true =>
      simp only [d86635, d87797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5105 q selected
  have h21 (q : Pattern) (selected : d86636 q = 0) : d87798 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86636, d87798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86636, d87798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d86637 q = 0) : d87799 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86637, d87799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d86637, d87799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d86639 q = 0) : d87801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86639, d87801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5106 q selected
    | true =>
      simp only [d86639, d87801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5087 q selected
  have h24 (q : Pattern) (selected : d86642 q = 0) : d87741 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86642, d87741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5107 q selected
    | true =>
      simp only [d86642, d87741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5108 q selected
  have h25 (q : Pattern) (selected : d86643 q = 0) : d87802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86643, d87802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d86643, d87802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d86645 q = 0) : d87804 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86645, d87804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5109 q selected
    | true =>
      simp only [d86645, d87804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d86646 q = 0) : d87805 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86646, d87805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d86646, d87805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d86647 q = 0) : d87806 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86647, d87806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d86647, d87806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d86648 q = 0) : d87807 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86648, d87807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d86648, d87807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d86649 q = 0) : d87808 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86649, d87808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d86649, d87808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d86650 q = 0) : d87809 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86650, d87809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d86650, d87809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro5111 (p : Pattern) (selected : d86657 p = 0) : d87816 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86548 q = 0) : d87731 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86548, d87731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5084 q selected
    | true =>
      simp only [d86548, d87731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5085 q selected
  have h2 (q : Pattern) (selected : d86549 q = 0) : d87732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86549, d87732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86549, d87732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86550 q = 0) : d87733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86550, d87733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86550, d87733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86551 q = 0) : d87734 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86551, d87734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86551, d87734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86552 q = 0) : d87735 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86552, d87735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86552, d87735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86652 q = 0) : d87811 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86652, d87811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5085 q selected
    | true =>
      simp only [d86652, d87811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86653 q = 0) : d87812 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86653, d87812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86653, d87812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86654 q = 0) : d87813 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86654, d87813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86654, d87813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d86655 q = 0) : d87814 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86655, d87814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86655, d87814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86656 q = 0) : d87815 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86656, d87815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86656, d87815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86657 q = 0) : d87816 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86657, d87816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86657, d87816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5112 (p : Pattern) (selected : d86663 p = 0) : d87822 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86652 q = 0) : d87811 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86652, d87811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5085 q selected
    | true =>
      simp only [d86652, d87811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86653 q = 0) : d87812 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86653, d87812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86653, d87812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86654 q = 0) : d87813 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86654, d87813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86654, d87813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86655 q = 0) : d87814 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86655, d87814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86655, d87814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86656 q = 0) : d87815 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86656, d87815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86656, d87815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86658 q = 0) : d87817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86658, d87817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5088 q selected
    | true =>
      simp only [d86658, d87817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86659 q = 0) : d87818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86659, d87818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86659, d87818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86660 q = 0) : d87819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86660, d87819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86660, d87819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d86661 q = 0) : d87820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86661, d87820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86661, d87820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86662 q = 0) : d87821 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86662, d87821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86662, d87821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86663 q = 0) : d87822 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86663, d87822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86663, d87822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5113 (p : Pattern) (selected : d86670 p = 0) : d87829 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86639 q = 0) : d87801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86639, d87801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5106 q selected
    | true =>
      simp only [d86639, d87801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5087 q selected
  have h2 (q : Pattern) (selected : d86642 q = 0) : d87741 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86642, d87741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5107 q selected
    | true =>
      simp only [d86642, d87741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5108 q selected
  have h3 (q : Pattern) (selected : d86643 q = 0) : d87802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86643, d87802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86643, d87802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86645 q = 0) : d87804 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86645, d87804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5109 q selected
    | true =>
      simp only [d86645, d87804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86646 q = 0) : d87805 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86646, d87805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86646, d87805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86647 q = 0) : d87806 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86647, d87806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86647, d87806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86668 q = 0) : d87827 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86668, d87827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86668, d87827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86669 q = 0) : d87828 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86669, d87828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86669, d87828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86670 q = 0) : d87829 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86670, d87829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86670, d87829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro5114 (p : Pattern) (selected : d86672 p = 0) : d87831 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86658 q = 0) : d87817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86658, d87817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5088 q selected
    | true =>
      simp only [d86658, d87817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86659 q = 0) : d87818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86659, d87818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86659, d87818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86660 q = 0) : d87819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86660, d87819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86660, d87819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86661 q = 0) : d87820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86661, d87820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86661, d87820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86662 q = 0) : d87821 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86662, d87821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86662, d87821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86672 q = 0) : d87831 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86672, d87831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86672, d87831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5115 (p : Pattern) (selected : d86683 p = 0) : d87842 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86678 q = 0) : d87837 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86678, d87837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86678, d87837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro526 q selected
  have h2 (q : Pattern) (selected : d86679 q = 0) : d87838 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86679, d87838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86679, d87838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86680 q = 0) : d87839 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86680, d87839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86680, d87839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro527 q selected
  have h4 (q : Pattern) (selected : d86681 q = 0) : d87840 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86681, d87840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86681, d87840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86682 q = 0) : d87841 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86682, d87841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86682, d87841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86683 q = 0) : d87842 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86683, d87842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86683, d87842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5116 (p : Pattern) (selected : d86689 p = 0) : d87848 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86680 q = 0) : d87839 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86680, d87839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86680, d87839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro527 q selected
  have h2 (q : Pattern) (selected : d86681 q = 0) : d87840 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86681, d87840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86681, d87840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86686 q = 0) : d87845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86686, d87845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86686, d87845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro528 q selected
  have h4 (q : Pattern) (selected : d86687 q = 0) : d87846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86687, d87846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86687, d87846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86688 q = 0) : d87847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86688, d87847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86688, d87847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86689 q = 0) : d87848 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86689, d87848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86689, d87848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5117 (p : Pattern) (selected : d86695 p = 0) : d87854 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86684 q = 0) : d87843 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86684, d87843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5115 q selected
    | true =>
      simp only [d86684, d87843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86685 q = 0) : d87844 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86685, d87844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86685, d87844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86690 q = 0) : d87849 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86690, d87849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5116 q selected
    | true =>
      simp only [d86690, d87849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86691 q = 0) : d87850 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86691, d87850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86691, d87850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86692 q = 0) : d87851 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86692, d87851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86692, d87851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86693 q = 0) : d87852 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86693, d87852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86693, d87852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86694 q = 0) : d87853 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86694, d87853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86694, d87853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86695 q = 0) : d87854 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86695, d87854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86695, d87854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5118 (p : Pattern) (selected : d86697 p = 0) : d87856 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86686 q = 0) : d87845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86686, d87845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86686, d87845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro528 q selected
  have h2 (q : Pattern) (selected : d86687 q = 0) : d87846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86687, d87846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86687, d87846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86696 q = 0) : d87855 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86696, d87855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86696, d87855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86697 q = 0) : d87856 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86697, d87856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86697, d87856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5119 (p : Pattern) (selected : d86703 p = 0) : d87862 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86690 q = 0) : d87849 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86690, d87849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5116 q selected
    | true =>
      simp only [d86690, d87849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86691 q = 0) : d87850 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86691, d87850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86691, d87850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86698 q = 0) : d87857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86698, d87857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5118 q selected
    | true =>
      simp only [d86698, d87857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86699 q = 0) : d87858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86699, d87858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86699, d87858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86700 q = 0) : d87859 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86700, d87859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86700, d87859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86701 q = 0) : d87860 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86701, d87860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86701, d87860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86702 q = 0) : d87861 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86702, d87861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86702, d87861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86703 q = 0) : d87862 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86703, d87862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86703, d87862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5120 (p : Pattern) (selected : d86710 p = 0) : d87848 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86705 q = 0) : d87839 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86705, d87839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86705, d87839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro535 q selected
  have h2 (q : Pattern) (selected : d86706 q = 0) : d87840 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86706, d87840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86706, d87840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86707 q = 0) : d87845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86707, d87845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86707, d87845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro536 q selected
  have h4 (q : Pattern) (selected : d86708 q = 0) : d87846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86708, d87846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86708, d87846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86709 q = 0) : d87847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86709, d87847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86709, d87847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86710 q = 0) : d87848 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86710, d87848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86710, d87848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5121 (p : Pattern) (selected : d86714 p = 0) : d87856 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86707 q = 0) : d87845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86707, d87845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86707, d87845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro536 q selected
  have h2 (q : Pattern) (selected : d86708 q = 0) : d87846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86708, d87846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86708, d87846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86713 q = 0) : d87855 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86713, d87855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86713, d87855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86714 q = 0) : d87856 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86714, d87856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86714, d87856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5122 (p : Pattern) (selected : d86720 p = 0) : d87862 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86711 q = 0) : d87849 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86711, d87849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5120 q selected
    | true =>
      simp only [d86711, d87849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86712 q = 0) : d87850 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86712, d87850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86712, d87850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86715 q = 0) : d87857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86715, d87857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5121 q selected
    | true =>
      simp only [d86715, d87857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86716 q = 0) : d87858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86716, d87858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86716, d87858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86717 q = 0) : d87859 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86717, d87859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86717, d87859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86718 q = 0) : d87860 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86718, d87860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86718, d87860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86719 q = 0) : d87861 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86719, d87861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86719, d87861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86720 q = 0) : d87862 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86720, d87862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86720, d87862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5123 (p : Pattern) (selected : d86724 p = 0) : d87867 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86715 q = 0) : d87857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86715, d87857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5121 q selected
    | true =>
      simp only [d86715, d87857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86716 q = 0) : d87858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86716, d87858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86716, d87858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86721 q = 0) : d87864 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86721, d87864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86721, d87864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86722 q = 0) : d87865 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86722, d87865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86722, d87865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86723 q = 0) : d87866 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86723, d87866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86723, d87866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86724 q = 0) : d87867 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86724, d87867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86724, d87867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5124 (p : Pattern) (selected : d86730 p = 0) : d87873 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86690 q = 0) : d87849 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86690, d87849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5116 q selected
    | true =>
      simp only [d86690, d87849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86691 q = 0) : d87850 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86691, d87850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86691, d87850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86727 q = 0) : d87870 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86727, d87870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86727, d87870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86728 q = 0) : d87871 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86728, d87871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86728, d87871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86729 q = 0) : d87872 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86729, d87872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86729, d87872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86730 q = 0) : d87873 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86730, d87873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86730, d87873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5125 (p : Pattern) (selected : d86736 p = 0) : d87879 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86704 q = 0) : d87863 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86704, d87863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5117 q selected
    | true =>
      simp only [d86704, d87863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5119 q selected
  have h2 (q : Pattern) (selected : d86725 q = 0) : d87868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86725, d87868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5122 q selected
    | true =>
      simp only [d86725, d87868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5123 q selected
  have h3 (q : Pattern) (selected : d86726 q = 0) : d87869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86726, d87869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86726, d87869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86731 q = 0) : d87874 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86731, d87874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5124 q selected
    | true =>
      simp only [d86731, d87874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86732 q = 0) : d87875 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86732, d87875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86732, d87875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86733 q = 0) : d87876 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86733, d87876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86733, d87876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86734 q = 0) : d87877 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86734, d87877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86734, d87877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86735 q = 0) : d87878 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86735, d87878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86735, d87878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86736 q = 0) : d87879 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86736, d87879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86736, d87879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro5126 (p : Pattern) (selected : d86741 p = 0) : d87867 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86698 q = 0) : d87857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86698, d87857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5118 q selected
    | true =>
      simp only [d86698, d87857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86699 q = 0) : d87858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86699, d87858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86699, d87858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86738 q = 0) : d87864 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86738, d87864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86738, d87864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86739 q = 0) : d87865 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86739, d87865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86739, d87865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86740 q = 0) : d87866 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86740, d87866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86740, d87866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86741 q = 0) : d87867 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86741, d87867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86741, d87867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5127 (p : Pattern) (selected : d86747 p = 0) : d87886 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86742 q = 0) : d87881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86742, d87881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5126 q selected
    | true =>
      simp only [d86742, d87881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86743 q = 0) : d87882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86743, d87882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86743, d87882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86744 q = 0) : d87883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86744, d87883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86744, d87883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86745 q = 0) : d87884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86745, d87884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86745, d87884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86746 q = 0) : d87885 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86746, d87885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86746, d87885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86747 q = 0) : d87886 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86747, d87886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86747, d87886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5128 (p : Pattern) (selected : d86753 p = 0) : d87892 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86554 q = 0) : d87737 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86554, d87737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86554, d87737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5086 q selected
  have h2 (q : Pattern) (selected : d86555 q = 0) : d87738 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86555, d87738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86555, d87738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d86564 q = 0) : d87747 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86564, d87747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5086 q selected
    | true =>
      simp only [d86564, d87747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5089 q selected
  have h4 (q : Pattern) (selected : d86565 q = 0) : d87748 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86565, d87748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86565, d87748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86566 q = 0) : d87749 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86566, d87749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86566, d87749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86651 q = 0) : d87810 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86651, d87810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5101 q selected
    | true =>
      simp only [d86651, d87810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5110 q selected
  have h7 (q : Pattern) (selected : d86664 q = 0) : d87823 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86664, d87823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5111 q selected
    | true =>
      simp only [d86664, d87823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5112 q selected
  have h8 (q : Pattern) (selected : d86665 q = 0) : d87824 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86665, d87824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86665, d87824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86666 q = 0) : d87825 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86666, d87825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d86666, d87825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d86667 q = 0) : d87826 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86667, d87826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86667, d87826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86671 q = 0) : d87830 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86671, d87830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86671, d87830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5113 q selected
  have h12 (q : Pattern) (selected : d86673 q = 0) : d87832 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86673, d87832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86673, d87832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5114 q selected
  have h13 (q : Pattern) (selected : d86674 q = 0) : d87833 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86674, d87833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d86674, d87833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d86675 q = 0) : d87834 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86675, d87834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d86675, d87834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d86676 q = 0) : d87835 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86676, d87835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d86676, d87835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d86677 q = 0) : d87836 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d86677, d87836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86677, d87836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d86737 q = 0) : d87880 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86737, d87880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86737, d87880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5125 q selected
  have h18 (q : Pattern) (selected : d86748 q = 0) : d87887 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86748, d87887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86748, d87887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5127 q selected
  have h19 (q : Pattern) (selected : d86749 q = 0) : d87888 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86749, d87888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d86749, d87888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d86750 q = 0) : d87889 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86750, d87889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d86750, d87889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d86751 q = 0) : d87890 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86751, d87890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d86751, d87890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d86752 q = 0) : d87891 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d86752, d87891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d86752, d87891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d86753 q = 0) : d87892 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d86753, d87892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d86753, d87892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro5129 (p : Pattern) (selected : d86759 p = 0) : d87898 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86754 q = 0) : d87893 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d86754, d87893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86754, d87893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5128 q selected
  have h2 (q : Pattern) (selected : d86755 q = 0) : d87894 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d86755, d87894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86755, d87894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86756 q = 0) : d87895 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d86756, d87895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86756, d87895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86757 q = 0) : d87896 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d86757, d87896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86757, d87896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86758 q = 0) : d87897 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d86758, d87897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86758, d87897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86759 q = 0) : d87898 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d86759, d87898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86759, d87898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5130 (p : Pattern) (selected : d86769 p = 0) : d87908 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86764 q = 0) : d87903 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86764, d87903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86764, d87903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro561 q selected
  have h2 (q : Pattern) (selected : d86765 q = 0) : d87904 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86765, d87904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86765, d87904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86766 q = 0) : d87905 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86766, d87905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86766, d87905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro563 q selected
  have h4 (q : Pattern) (selected : d86767 q = 0) : d87906 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86767, d87906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86767, d87906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86768 q = 0) : d87907 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86768, d87907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86768, d87907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86769 q = 0) : d87908 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86769, d87908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86769, d87908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5131 (p : Pattern) (selected : d86773 p = 0) : d87912 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86766 q = 0) : d87905 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86766, d87905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86766, d87905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro563 q selected
  have h2 (q : Pattern) (selected : d86767 q = 0) : d87906 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86767, d87906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86767, d87906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86772 q = 0) : d87911 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86772, d87911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86772, d87911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86773 q = 0) : d87912 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86773, d87912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86773, d87912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5132 (p : Pattern) (selected : d86779 p = 0) : d87918 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86770 q = 0) : d87909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86770, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5130 q selected
    | true =>
      simp only [d86770, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86771 q = 0) : d87910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86771, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86771, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86774 q = 0) : d87913 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5131 q selected
    | true =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86775 q = 0) : d87914 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86776 q = 0) : d87915 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86776, d87915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86776, d87915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86777 q = 0) : d87916 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86777, d87916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86777, d87916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86778 q = 0) : d87917 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86778, d87917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86778, d87917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86779 q = 0) : d87918 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86779, d87918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86779, d87918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5133 (p : Pattern) (selected : d86783 p = 0) : d87922 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86774 q = 0) : d87913 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5131 q selected
    | true =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86775 q = 0) : d87914 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86780 q = 0) : d87919 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86780, d87919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86780, d87919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86781 q = 0) : d87920 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86781, d87920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86781, d87920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86782 q = 0) : d87921 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86782, d87921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86782, d87921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86783 q = 0) : d87922 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86783, d87922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86783, d87922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5134 (p : Pattern) (selected : d86789 p = 0) : d87928 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86784 q = 0) : d87923 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86784, d87923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5132 q selected
    | true =>
      simp only [d86784, d87923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5133 q selected
  have h2 (q : Pattern) (selected : d86785 q = 0) : d87924 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86785, d87924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86785, d87924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86786 q = 0) : d87925 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86786, d87925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86786, d87925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86787 q = 0) : d87926 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86787, d87926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86787, d87926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86788 q = 0) : d87927 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86788, d87927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86788, d87927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86789 q = 0) : d87928 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86789, d87928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86789, d87928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5135 (p : Pattern) (selected : d86792 p = 0) : d87931 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86770 q = 0) : d87909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86770, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5130 q selected
    | true =>
      simp only [d86770, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86771 q = 0) : d87910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86771, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86771, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86774 q = 0) : d87913 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5131 q selected
    | true =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86775 q = 0) : d87914 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86776 q = 0) : d87915 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86776, d87915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86776, d87915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86777 q = 0) : d87916 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86777, d87916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86777, d87916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86778 q = 0) : d87917 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86778, d87917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86778, d87917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86792 q = 0) : d87931 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86792, d87931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86792, d87931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5136 (p : Pattern) (selected : d86793 p = 0) : d87932 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86774 q = 0) : d87913 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5131 q selected
    | true =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86775 q = 0) : d87914 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86780 q = 0) : d87919 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86780, d87919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86780, d87919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86781 q = 0) : d87920 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86781, d87920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86781, d87920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86782 q = 0) : d87921 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86782, d87921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86782, d87921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86793 q = 0) : d87932 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86793, d87932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86793, d87932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5137 (p : Pattern) (selected : d86799 p = 0) : d87938 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86784 q = 0) : d87923 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86784, d87923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5132 q selected
    | true =>
      simp only [d86784, d87923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5133 q selected
  have h2 (q : Pattern) (selected : d86785 q = 0) : d87924 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86785, d87924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86785, d87924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86786 q = 0) : d87925 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86786, d87925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86786, d87925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86787 q = 0) : d87926 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86787, d87926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86787, d87926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86788 q = 0) : d87927 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86788, d87927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86788, d87927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86794 q = 0) : d87933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86794, d87933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5135 q selected
    | true =>
      simp only [d86794, d87933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5136 q selected
  have h7 (q : Pattern) (selected : d86795 q = 0) : d87934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86795, d87934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86795, d87934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86796 q = 0) : d87935 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86796, d87935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86796, d87935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d86797 q = 0) : d87936 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86797, d87936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86797, d87936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86798 q = 0) : d87937 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86798, d87937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86798, d87937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86799 q = 0) : d87938 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86799, d87938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86799, d87938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5138 (p : Pattern) (selected : d86804 p = 0) : d87943 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86770 q = 0) : d87909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86770, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5130 q selected
    | true =>
      simp only [d86770, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86771 q = 0) : d87910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86771, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86771, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86774 q = 0) : d87913 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5131 q selected
    | true =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86775 q = 0) : d87914 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86776 q = 0) : d87915 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86776, d87915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86776, d87915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86777 q = 0) : d87916 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86777, d87916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86777, d87916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86803 q = 0) : d87942 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86803, d87942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86803, d87942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86804 q = 0) : d87943 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86804, d87943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86804, d87943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5139 (p : Pattern) (selected : d86806 p = 0) : d87945 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86774 q = 0) : d87913 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5131 q selected
    | true =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86775 q = 0) : d87914 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86780 q = 0) : d87919 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86780, d87919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86780, d87919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86781 q = 0) : d87920 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86781, d87920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86781, d87920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86805 q = 0) : d87944 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86805, d87944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86805, d87944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86806 q = 0) : d87945 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86806, d87945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86806, d87945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5140 (p : Pattern) (selected : d86813 p = 0) : d87952 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86770 q = 0) : d87909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86770, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5130 q selected
    | true =>
      simp only [d86770, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86771 q = 0) : d87910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86771, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86771, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86774 q = 0) : d87913 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5131 q selected
    | true =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86775 q = 0) : d87914 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86776 q = 0) : d87915 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86776, d87915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86776, d87915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86811 q = 0) : d87950 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86811, d87950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86811, d87950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86812 q = 0) : d87951 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86812, d87951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86812, d87951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86813 q = 0) : d87952 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86813, d87952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86813, d87952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5141 (p : Pattern) (selected : d86816 p = 0) : d87955 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86774 q = 0) : d87913 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5131 q selected
    | true =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86775 q = 0) : d87914 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86780 q = 0) : d87919 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86780, d87919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86780, d87919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86814 q = 0) : d87953 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86814, d87953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86814, d87953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86815 q = 0) : d87954 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86815, d87954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86815, d87954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86816 q = 0) : d87955 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86816, d87955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86816, d87955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5142 (p : Pattern) (selected : d86823 p = 0) : d87962 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86820 q = 0) : d87959 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86820, d87959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86820, d87959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro560 q selected
  have h2 (q : Pattern) (selected : d86821 q = 0) : d87960 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86821, d87960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86821, d87960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86764 q = 0) : d87903 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86764, d87903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86764, d87903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro561 q selected
  have h4 (q : Pattern) (selected : d86765 q = 0) : d87904 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86765, d87904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86765, d87904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86822 q = 0) : d87961 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86822, d87961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86822, d87961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86823 q = 0) : d87962 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86823, d87962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86823, d87962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5143 (p : Pattern) (selected : d86829 p = 0) : d87968 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86824 q = 0) : d87963 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86824, d87963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5142 q selected
    | true =>
      simp only [d86824, d87963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86825 q = 0) : d87964 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86825, d87964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86825, d87964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86770 q = 0) : d87909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86770, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5130 q selected
    | true =>
      simp only [d86770, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86771 q = 0) : d87910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86771, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86771, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86826 q = 0) : d87965 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86826, d87965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86826, d87965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86827 q = 0) : d87966 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86827, d87966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86827, d87966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86828 q = 0) : d87967 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86828, d87967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86828, d87967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86829 q = 0) : d87968 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86829, d87968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86829, d87968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5144 (p : Pattern) (selected : d86836 p = 0) : d87908 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86831 q = 0) : d87903 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86831, d87903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86831, d87903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro595 q selected
  have h2 (q : Pattern) (selected : d86832 q = 0) : d87904 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86832, d87904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86832, d87904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86833 q = 0) : d87905 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86833, d87905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86833, d87905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro597 q selected
  have h4 (q : Pattern) (selected : d86834 q = 0) : d87906 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86834, d87906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86834, d87906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86835 q = 0) : d87907 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86835, d87907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86835, d87907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86836 q = 0) : d87908 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86836, d87908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86836, d87908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5145 (p : Pattern) (selected : d86840 p = 0) : d87912 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86833 q = 0) : d87905 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86833, d87905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86833, d87905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro597 q selected
  have h2 (q : Pattern) (selected : d86834 q = 0) : d87906 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86834, d87906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86834, d87906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86839 q = 0) : d87911 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86839, d87911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86839, d87911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86840 q = 0) : d87912 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86840, d87912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86840, d87912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5146 (p : Pattern) (selected : d86846 p = 0) : d87918 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86837 q = 0) : d87909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86837, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5144 q selected
    | true =>
      simp only [d86837, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86838 q = 0) : d87910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86838, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86838, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86841 q = 0) : d87913 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86841, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5145 q selected
    | true =>
      simp only [d86841, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86842 q = 0) : d87914 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86842, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86842, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86843 q = 0) : d87915 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86843, d87915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86843, d87915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86844 q = 0) : d87916 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86844, d87916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86844, d87916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86845 q = 0) : d87917 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86845, d87917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86845, d87917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86846 q = 0) : d87918 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86846, d87918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86846, d87918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5147 (p : Pattern) (selected : d86850 p = 0) : d87922 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86841 q = 0) : d87913 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86841, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5145 q selected
    | true =>
      simp only [d86841, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86842 q = 0) : d87914 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86842, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86842, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86847 q = 0) : d87919 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86847, d87919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86847, d87919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86848 q = 0) : d87920 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86848, d87920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86848, d87920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86849 q = 0) : d87921 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86849, d87921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86849, d87921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86850 q = 0) : d87922 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86850, d87922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86850, d87922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5148 (p : Pattern) (selected : d86856 p = 0) : d87974 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86770 q = 0) : d87909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86770, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5130 q selected
    | true =>
      simp only [d86770, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86771 q = 0) : d87910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86771, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86771, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86853 q = 0) : d87971 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86853, d87971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86853, d87971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86854 q = 0) : d87972 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86854, d87972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86854, d87972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86855 q = 0) : d87973 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86855, d87973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86855, d87973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86856 q = 0) : d87974 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86856, d87974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86856, d87974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5149 (p : Pattern) (selected : d86862 p = 0) : d87980 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86807 q = 0) : d87946 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86807, d87946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5138 q selected
    | true =>
      simp only [d86807, d87946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5139 q selected
  have h2 (q : Pattern) (selected : d86808 q = 0) : d87947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86808, d87947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86808, d87947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86809 q = 0) : d87948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86809, d87948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86809, d87948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86810 q = 0) : d87949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86810, d87949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86810, d87949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86817 q = 0) : d87956 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86817, d87956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5140 q selected
    | true =>
      simp only [d86817, d87956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5141 q selected
  have h6 (q : Pattern) (selected : d86818 q = 0) : d87957 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86818, d87957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86818, d87957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86819 q = 0) : d87958 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86819, d87958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86819, d87958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86830 q = 0) : d87969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86830, d87969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5143 q selected
    | true =>
      simp only [d86830, d87969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5132 q selected
  have h9 (q : Pattern) (selected : d86851 q = 0) : d87923 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86851, d87923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5146 q selected
    | true =>
      simp only [d86851, d87923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5147 q selected
  have h10 (q : Pattern) (selected : d86852 q = 0) : d87970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86852, d87970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d86852, d87970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86857 q = 0) : d87975 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86857, d87975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5148 q selected
    | true =>
      simp only [d86857, d87975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d86858 q = 0) : d87976 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86858, d87976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d86858, d87976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d86859 q = 0) : d87977 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86859, d87977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86859, d87977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d86860 q = 0) : d87978 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86860, d87978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86860, d87978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d86861 q = 0) : d87979 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86861, d87979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86861, d87979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d86862 q = 0) : d87980 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86862, d87980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86862, d87980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro5150 (p : Pattern) (selected : d86863 p = 0) : d87981 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86770 q = 0) : d87909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86770, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5130 q selected
    | true =>
      simp only [d86770, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86771 q = 0) : d87910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86771, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86771, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86774 q = 0) : d87913 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5131 q selected
    | true =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86775 q = 0) : d87914 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86776 q = 0) : d87915 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86776, d87915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86776, d87915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86777 q = 0) : d87916 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86777, d87916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86777, d87916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86803 q = 0) : d87942 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86803, d87942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86803, d87942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86863 q = 0) : d87981 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86863, d87981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86863, d87981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5151 (p : Pattern) (selected : d86864 p = 0) : d87982 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86774 q = 0) : d87913 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5131 q selected
    | true =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86775 q = 0) : d87914 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86780 q = 0) : d87919 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86780, d87919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86780, d87919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86781 q = 0) : d87920 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86781, d87920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86781, d87920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86805 q = 0) : d87944 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86805, d87944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86805, d87944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86864 q = 0) : d87982 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86864, d87982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86864, d87982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5152 (p : Pattern) (selected : d86869 p = 0) : d87987 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86770 q = 0) : d87909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86770, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5130 q selected
    | true =>
      simp only [d86770, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86771 q = 0) : d87910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86771, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86771, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86774 q = 0) : d87913 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5131 q selected
    | true =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86775 q = 0) : d87914 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86776 q = 0) : d87915 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86776, d87915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86776, d87915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86811 q = 0) : d87950 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86811, d87950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86811, d87950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86812 q = 0) : d87951 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86812, d87951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86812, d87951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86869 q = 0) : d87987 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86869, d87987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86869, d87987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5153 (p : Pattern) (selected : d86870 p = 0) : d87988 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86774 q = 0) : d87913 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5131 q selected
    | true =>
      simp only [d86774, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86775 q = 0) : d87914 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86775, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86780 q = 0) : d87919 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86780, d87919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86780, d87919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86814 q = 0) : d87953 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86814, d87953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86814, d87953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86815 q = 0) : d87954 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86815, d87954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86815, d87954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86870 q = 0) : d87988 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86870, d87988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86870, d87988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5154 (p : Pattern) (selected : d86874 p = 0) : d87992 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86824 q = 0) : d87963 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86824, d87963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5142 q selected
    | true =>
      simp only [d86824, d87963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86825 q = 0) : d87964 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86825, d87964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86825, d87964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86770 q = 0) : d87909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86770, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5130 q selected
    | true =>
      simp only [d86770, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86771 q = 0) : d87910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86771, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86771, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86826 q = 0) : d87965 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86826, d87965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86826, d87965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86827 q = 0) : d87966 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86827, d87966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86827, d87966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86828 q = 0) : d87967 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86828, d87967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86828, d87967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86874 q = 0) : d87992 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86874, d87992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86874, d87992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5155 (p : Pattern) (selected : d86876 p = 0) : d87931 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86837 q = 0) : d87909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86837, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5144 q selected
    | true =>
      simp only [d86837, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86838 q = 0) : d87910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86838, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86838, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86841 q = 0) : d87913 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86841, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5145 q selected
    | true =>
      simp only [d86841, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86842 q = 0) : d87914 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86842, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86842, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86843 q = 0) : d87915 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86843, d87915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86843, d87915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86844 q = 0) : d87916 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86844, d87916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86844, d87916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86845 q = 0) : d87917 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86845, d87917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86845, d87917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86876 q = 0) : d87931 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86876, d87931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86876, d87931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5156 (p : Pattern) (selected : d86877 p = 0) : d87932 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86841 q = 0) : d87913 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86841, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5145 q selected
    | true =>
      simp only [d86841, d87913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86842 q = 0) : d87914 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86842, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86842, d87914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86847 q = 0) : d87919 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86847, d87919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86847, d87919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86848 q = 0) : d87920 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86848, d87920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86848, d87920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86849 q = 0) : d87921 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86849, d87921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86849, d87921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86877 q = 0) : d87932 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86877, d87932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86877, d87932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5157 (p : Pattern) (selected : d86880 p = 0) : d87995 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86770 q = 0) : d87909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86770, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5130 q selected
    | true =>
      simp only [d86770, d87909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86771 q = 0) : d87910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86771, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86771, d87910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86853 q = 0) : d87971 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86853, d87971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86853, d87971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86854 q = 0) : d87972 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86854, d87972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86854, d87972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86855 q = 0) : d87973 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86855, d87973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86855, d87973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86880 q = 0) : d87995 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86880, d87995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86880, d87995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5158 (p : Pattern) (selected : d86886 p = 0) : d88001 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86807 q = 0) : d87946 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86807, d87946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5138 q selected
    | true =>
      simp only [d86807, d87946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5139 q selected
  have h2 (q : Pattern) (selected : d86808 q = 0) : d87947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86808, d87947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86808, d87947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86809 q = 0) : d87948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86809, d87948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86809, d87948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86810 q = 0) : d87949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86810, d87949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86810, d87949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86817 q = 0) : d87956 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86817, d87956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5140 q selected
    | true =>
      simp only [d86817, d87956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5141 q selected
  have h6 (q : Pattern) (selected : d86818 q = 0) : d87957 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86818, d87957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86818, d87957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86819 q = 0) : d87958 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86819, d87958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86819, d87958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86830 q = 0) : d87969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86830, d87969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5143 q selected
    | true =>
      simp only [d86830, d87969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5132 q selected
  have h9 (q : Pattern) (selected : d86851 q = 0) : d87923 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86851, d87923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5146 q selected
    | true =>
      simp only [d86851, d87923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5147 q selected
  have h10 (q : Pattern) (selected : d86852 q = 0) : d87970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86852, d87970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d86852, d87970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86857 q = 0) : d87975 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86857, d87975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5148 q selected
    | true =>
      simp only [d86857, d87975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d86858 q = 0) : d87976 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86858, d87976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d86858, d87976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d86859 q = 0) : d87977 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86859, d87977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86859, d87977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d86860 q = 0) : d87978 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86860, d87978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86860, d87978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d86861 q = 0) : d87979 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86861, d87979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86861, d87979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d86865 q = 0) : d87983 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86865, d87983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5150 q selected
    | true =>
      simp only [d86865, d87983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5151 q selected
  have h17 (q : Pattern) (selected : d86866 q = 0) : d87984 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86866, d87984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86866, d87984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d86867 q = 0) : d87985 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86867, d87985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d86867, d87985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d86868 q = 0) : d87986 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86868, d87986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86868, d87986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d86871 q = 0) : d87989 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86871, d87989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5152 q selected
    | true =>
      simp only [d86871, d87989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5153 q selected
  have h21 (q : Pattern) (selected : d86872 q = 0) : d87990 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86872, d87990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86872, d87990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d86873 q = 0) : d87991 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86873, d87991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d86873, d87991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d86875 q = 0) : d87993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86875, d87993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5154 q selected
    | true =>
      simp only [d86875, d87993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5135 q selected
  have h24 (q : Pattern) (selected : d86878 q = 0) : d87933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86878, d87933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5155 q selected
    | true =>
      simp only [d86878, d87933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5156 q selected
  have h25 (q : Pattern) (selected : d86879 q = 0) : d87994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86879, d87994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d86879, d87994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d86881 q = 0) : d87996 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86881, d87996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5157 q selected
    | true =>
      simp only [d86881, d87996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d86882 q = 0) : d87997 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86882, d87997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d86882, d87997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d86883 q = 0) : d87998 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86883, d87998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d86883, d87998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d86884 q = 0) : d87999 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86884, d87999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d86884, d87999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d86885 q = 0) : d88000 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86885, d88000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d86885, d88000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d86886 q = 0) : d88001 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86886, d88001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d86886, d88001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro5159 (p : Pattern) (selected : d86893 p = 0) : d88008 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86784 q = 0) : d87923 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86784, d87923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5132 q selected
    | true =>
      simp only [d86784, d87923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5133 q selected
  have h2 (q : Pattern) (selected : d86785 q = 0) : d87924 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86785, d87924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86785, d87924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86786 q = 0) : d87925 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86786, d87925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86786, d87925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86787 q = 0) : d87926 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86787, d87926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86787, d87926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86788 q = 0) : d87927 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86788, d87927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86788, d87927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86888 q = 0) : d88003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86888, d88003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5133 q selected
    | true =>
      simp only [d86888, d88003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86889 q = 0) : d88004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86889, d88004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86889, d88004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86890 q = 0) : d88005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86890, d88005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86890, d88005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d86891 q = 0) : d88006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86891, d88006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86891, d88006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86892 q = 0) : d88007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86892, d88007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86892, d88007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86893 q = 0) : d88008 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86893, d88008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86893, d88008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5160 (p : Pattern) (selected : d86899 p = 0) : d88014 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86888 q = 0) : d88003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86888, d88003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5133 q selected
    | true =>
      simp only [d86888, d88003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86889 q = 0) : d88004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86889, d88004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86889, d88004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86890 q = 0) : d88005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86890, d88005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86890, d88005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86891 q = 0) : d88006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86891, d88006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86891, d88006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86892 q = 0) : d88007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86892, d88007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86892, d88007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86894 q = 0) : d88009 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86894, d88009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5136 q selected
    | true =>
      simp only [d86894, d88009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86895 q = 0) : d88010 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86895, d88010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86895, d88010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86896 q = 0) : d88011 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86896, d88011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86896, d88011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d86897 q = 0) : d88012 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86897, d88012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86897, d88012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86898 q = 0) : d88013 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86898, d88013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86898, d88013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86899 q = 0) : d88014 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86899, d88014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86899, d88014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5161 (p : Pattern) (selected : d86906 p = 0) : d88021 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86875 q = 0) : d87993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86875, d87993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5154 q selected
    | true =>
      simp only [d86875, d87993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5135 q selected
  have h2 (q : Pattern) (selected : d86878 q = 0) : d87933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86878, d87933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5155 q selected
    | true =>
      simp only [d86878, d87933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5156 q selected
  have h3 (q : Pattern) (selected : d86879 q = 0) : d87994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86879, d87994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86879, d87994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86881 q = 0) : d87996 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86881, d87996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5157 q selected
    | true =>
      simp only [d86881, d87996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86882 q = 0) : d87997 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86882, d87997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86882, d87997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86883 q = 0) : d87998 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86883, d87998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86883, d87998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86904 q = 0) : d88019 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86904, d88019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86904, d88019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86905 q = 0) : d88020 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86905, d88020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86905, d88020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86906 q = 0) : d88021 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86906, d88021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86906, d88021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro5162 (p : Pattern) (selected : d86908 p = 0) : d88023 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86894 q = 0) : d88009 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86894, d88009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5136 q selected
    | true =>
      simp only [d86894, d88009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86895 q = 0) : d88010 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86895, d88010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86895, d88010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86896 q = 0) : d88011 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86896, d88011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86896, d88011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86897 q = 0) : d88012 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86897, d88012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86897, d88012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86898 q = 0) : d88013 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86898, d88013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86898, d88013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86908 q = 0) : d88023 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86908, d88023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86908, d88023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5163 (p : Pattern) (selected : d86919 p = 0) : d88034 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86914 q = 0) : d88029 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86914, d88029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86914, d88029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro616 q selected
  have h2 (q : Pattern) (selected : d86915 q = 0) : d88030 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86915, d88030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86915, d88030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86916 q = 0) : d88031 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86916, d88031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86916, d88031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro617 q selected
  have h4 (q : Pattern) (selected : d86917 q = 0) : d88032 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86917, d88032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86917, d88032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86918 q = 0) : d88033 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86918, d88033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86918, d88033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86919 q = 0) : d88034 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86919, d88034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86919, d88034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5164 (p : Pattern) (selected : d86925 p = 0) : d88040 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86916 q = 0) : d88031 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86916, d88031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86916, d88031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro617 q selected
  have h2 (q : Pattern) (selected : d86917 q = 0) : d88032 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86917, d88032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86917, d88032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86922 q = 0) : d88037 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86922, d88037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86922, d88037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro618 q selected
  have h4 (q : Pattern) (selected : d86923 q = 0) : d88038 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86923, d88038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86923, d88038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86924 q = 0) : d88039 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86924, d88039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86924, d88039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86925 q = 0) : d88040 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86925, d88040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86925, d88040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5165 (p : Pattern) (selected : d86931 p = 0) : d88046 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86920 q = 0) : d88035 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86920, d88035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5163 q selected
    | true =>
      simp only [d86920, d88035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86921 q = 0) : d88036 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86921, d88036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86921, d88036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86926 q = 0) : d88041 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86926, d88041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5164 q selected
    | true =>
      simp only [d86926, d88041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86927 q = 0) : d88042 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86927, d88042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86927, d88042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86928 q = 0) : d88043 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86928, d88043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86928, d88043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86929 q = 0) : d88044 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86929, d88044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86929, d88044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86930 q = 0) : d88045 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86930, d88045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86930, d88045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86931 q = 0) : d88046 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86931, d88046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86931, d88046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5166 (p : Pattern) (selected : d86933 p = 0) : d88048 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86922 q = 0) : d88037 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86922, d88037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86922, d88037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro618 q selected
  have h2 (q : Pattern) (selected : d86923 q = 0) : d88038 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86923, d88038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86923, d88038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86932 q = 0) : d88047 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86932, d88047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86932, d88047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86933 q = 0) : d88048 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86933, d88048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86933, d88048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5167 (p : Pattern) (selected : d86939 p = 0) : d88054 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86926 q = 0) : d88041 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86926, d88041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5164 q selected
    | true =>
      simp only [d86926, d88041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86927 q = 0) : d88042 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86927, d88042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86927, d88042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86934 q = 0) : d88049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86934, d88049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5166 q selected
    | true =>
      simp only [d86934, d88049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86935 q = 0) : d88050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86935, d88050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86935, d88050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86936 q = 0) : d88051 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86936, d88051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86936, d88051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86937 q = 0) : d88052 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86937, d88052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86937, d88052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86938 q = 0) : d88053 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86938, d88053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86938, d88053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86939 q = 0) : d88054 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86939, d88054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86939, d88054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5168 (p : Pattern) (selected : d86946 p = 0) : d88040 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86941 q = 0) : d88031 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86941, d88031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86941, d88031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro625 q selected
  have h2 (q : Pattern) (selected : d86942 q = 0) : d88032 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86942, d88032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86942, d88032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86943 q = 0) : d88037 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86943, d88037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86943, d88037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro626 q selected
  have h4 (q : Pattern) (selected : d86944 q = 0) : d88038 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86944, d88038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86944, d88038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86945 q = 0) : d88039 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86945, d88039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86945, d88039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86946 q = 0) : d88040 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86946, d88040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86946, d88040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5169 (p : Pattern) (selected : d86950 p = 0) : d88048 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86943 q = 0) : d88037 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86943, d88037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86943, d88037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro626 q selected
  have h2 (q : Pattern) (selected : d86944 q = 0) : d88038 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86944, d88038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86944, d88038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86949 q = 0) : d88047 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86949, d88047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86949, d88047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86950 q = 0) : d88048 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86950, d88048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86950, d88048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5170 (p : Pattern) (selected : d86956 p = 0) : d88054 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86947 q = 0) : d88041 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86947, d88041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5168 q selected
    | true =>
      simp only [d86947, d88041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86948 q = 0) : d88042 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86948, d88042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86948, d88042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86951 q = 0) : d88049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86951, d88049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5169 q selected
    | true =>
      simp only [d86951, d88049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86952 q = 0) : d88050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86952, d88050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86952, d88050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86953 q = 0) : d88051 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86953, d88051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86953, d88051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86954 q = 0) : d88052 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86954, d88052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86954, d88052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86955 q = 0) : d88053 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86955, d88053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86955, d88053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86956 q = 0) : d88054 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86956, d88054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86956, d88054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5171 (p : Pattern) (selected : d86960 p = 0) : d88059 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86951 q = 0) : d88049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86951, d88049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5169 q selected
    | true =>
      simp only [d86951, d88049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86952 q = 0) : d88050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86952, d88050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86952, d88050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86957 q = 0) : d88056 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86957, d88056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86957, d88056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86958 q = 0) : d88057 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86958, d88057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86958, d88057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86959 q = 0) : d88058 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86959, d88058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86959, d88058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86960 q = 0) : d88059 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86960, d88059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86960, d88059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5172 (p : Pattern) (selected : d86966 p = 0) : d88065 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86926 q = 0) : d88041 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86926, d88041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5164 q selected
    | true =>
      simp only [d86926, d88041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86927 q = 0) : d88042 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86927, d88042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86927, d88042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86963 q = 0) : d88062 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86963, d88062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86963, d88062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86964 q = 0) : d88063 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86964, d88063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86964, d88063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86965 q = 0) : d88064 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86965, d88064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86965, d88064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86966 q = 0) : d88065 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86966, d88065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86966, d88065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5173 (p : Pattern) (selected : d86972 p = 0) : d88071 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86940 q = 0) : d88055 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86940, d88055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5165 q selected
    | true =>
      simp only [d86940, d88055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5167 q selected
  have h2 (q : Pattern) (selected : d86961 q = 0) : d88060 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86961, d88060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5170 q selected
    | true =>
      simp only [d86961, d88060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5171 q selected
  have h3 (q : Pattern) (selected : d86962 q = 0) : d88061 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86962, d88061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86962, d88061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86967 q = 0) : d88066 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86967, d88066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5172 q selected
    | true =>
      simp only [d86967, d88066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86968 q = 0) : d88067 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86968, d88067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86968, d88067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86969 q = 0) : d88068 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86969, d88068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86969, d88068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86970 q = 0) : d88069 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86970, d88069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86970, d88069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86971 q = 0) : d88070 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86971, d88070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86971, d88070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86972 q = 0) : d88071 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86972, d88071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86972, d88071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro5174 (p : Pattern) (selected : d86977 p = 0) : d88059 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86934 q = 0) : d88049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86934, d88049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5166 q selected
    | true =>
      simp only [d86934, d88049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86935 q = 0) : d88050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86935, d88050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86935, d88050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86974 q = 0) : d88056 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86974, d88056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86974, d88056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86975 q = 0) : d88057 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86975, d88057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86975, d88057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86976 q = 0) : d88058 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86976, d88058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86976, d88058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86977 q = 0) : d88059 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86977, d88059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86977, d88059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5175 (p : Pattern) (selected : d86983 p = 0) : d88078 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86978 q = 0) : d88073 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86978, d88073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5174 q selected
    | true =>
      simp only [d86978, d88073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86979 q = 0) : d88074 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86979, d88074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86979, d88074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86980 q = 0) : d88075 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86980, d88075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86980, d88075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86981 q = 0) : d88076 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86981, d88076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86981, d88076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86982 q = 0) : d88077 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86982, d88077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86982, d88077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86983 q = 0) : d88078 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86983, d88078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86983, d88078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5176 (p : Pattern) (selected : d86989 p = 0) : d88084 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86790 q = 0) : d87929 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86790, d87929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86790, d87929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5134 q selected
  have h2 (q : Pattern) (selected : d86791 q = 0) : d87930 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86791, d87930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86791, d87930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d86800 q = 0) : d87939 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86800, d87939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5134 q selected
    | true =>
      simp only [d86800, d87939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5137 q selected
  have h4 (q : Pattern) (selected : d86801 q = 0) : d87940 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86801, d87940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86801, d87940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86802 q = 0) : d87941 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86802, d87941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86802, d87941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86887 q = 0) : d88002 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86887, d88002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5149 q selected
    | true =>
      simp only [d86887, d88002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5158 q selected
  have h7 (q : Pattern) (selected : d86900 q = 0) : d88015 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86900, d88015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5159 q selected
    | true =>
      simp only [d86900, d88015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5160 q selected
  have h8 (q : Pattern) (selected : d86901 q = 0) : d88016 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86901, d88016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86901, d88016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86902 q = 0) : d88017 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86902, d88017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d86902, d88017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d86903 q = 0) : d88018 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86903, d88018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86903, d88018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86907 q = 0) : d88022 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86907, d88022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86907, d88022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5161 q selected
  have h12 (q : Pattern) (selected : d86909 q = 0) : d88024 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86909, d88024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86909, d88024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5162 q selected
  have h13 (q : Pattern) (selected : d86910 q = 0) : d88025 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86910, d88025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d86910, d88025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d86911 q = 0) : d88026 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86911, d88026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d86911, d88026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d86912 q = 0) : d88027 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86912, d88027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d86912, d88027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d86913 q = 0) : d88028 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d86913, d88028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86913, d88028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d86973 q = 0) : d88072 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86973, d88072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86973, d88072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5173 q selected
  have h18 (q : Pattern) (selected : d86984 q = 0) : d88079 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86984, d88079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86984, d88079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5175 q selected
  have h19 (q : Pattern) (selected : d86985 q = 0) : d88080 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86985, d88080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d86985, d88080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d86986 q = 0) : d88081 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86986, d88081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d86986, d88081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d86987 q = 0) : d88082 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86987, d88082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d86987, d88082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d86988 q = 0) : d88083 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d86988, d88083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d86988, d88083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d86989 q = 0) : d88084 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d86989, d88084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d86989, d88084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro5177 (p : Pattern) (selected : d86995 p = 0) : d88090 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86990 q = 0) : d88085 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d86990, d88085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86990, d88085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5176 q selected
  have h2 (q : Pattern) (selected : d86991 q = 0) : d88086 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d86991, d88086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86991, d88086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86992 q = 0) : d88087 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d86992, d88087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86992, d88087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86993 q = 0) : d88088 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d86993, d88088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86993, d88088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86994 q = 0) : d88089 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d86994, d88089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86994, d88089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86995 q = 0) : d88090 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d86995, d88090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86995, d88090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5178 (p : Pattern) (selected : d87001 p = 0) : d88096 p = 1 := by
  have h0 (q : Pattern) (selected : d86058 q = 0) : d87329 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d86058, d87329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4957 q selected
    | true =>
      simp only [d86058, d87329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4985 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d86291 q = 0) : d87518 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d86291, d87518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86291, d87518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5033 q selected
  have h3 (q : Pattern) (selected : d86292 q = 0) : d87519 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d86292, d87519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86292, d87519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86525 q = 0) : d87708 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d86525, d87708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86525, d87708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5081 q selected
  have h5 (q : Pattern) (selected : d86526 q = 0) : d87709 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d86526, d87709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86526, d87709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86527 q = 0) : d87710 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d86527, d87710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86527, d87710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86760 q = 0) : d87899 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d86760, d87899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86760, d87899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5129 q selected
  have h8 (q : Pattern) (selected : d86761 q = 0) : d87900 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d86761, d87900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86761, d87900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86762 q = 0) : d87901 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d86762, d87901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86762, d87901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86763 q = 0) : d87902 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d86763, d87902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86763, d87902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86996 q = 0) : d88091 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d86996, d88091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86996, d88091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5177 q selected
  have h12 (q : Pattern) (selected : d86997 q = 0) : d88092 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d86997, d88092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86997, d88092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d86998 q = 0) : d88093 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d86998, d88093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86998, d88093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d86999 q = 0) : d88094 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d86999, d88094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86999, d88094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d87000 q = 0) : d88095 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d87000, d88095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d87000, d88095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d87001 q = 0) : d88096 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d87001, d88096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d87001, d88096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro5179 (p : Pattern) (selected : d87007 p = 0) : d88102 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d87002 q = 0) : d88097 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d87002, d88097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5178 q selected
    | true =>
      simp only [d87002, d88097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d87003 q = 0) : d88098 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d87003, d88098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d87003, d88098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d87004 q = 0) : d88099 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d87004, d88099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d87004, d88099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d87005 q = 0) : d88100 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d87005, d88100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d87005, d88100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d87006 q = 0) : d88101 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d87006, d88101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d87006, d88101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d87007 q = 0) : d88102 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d87007, d88102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d87007, d88102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5180 (p : Pattern) (selected : d87013 p = 0) : d88108 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d87008 q = 0) : d88103 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d87008, d88103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5179 q selected
    | true =>
      simp only [d87008, d88103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d87009 q = 0) : d88104 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d87009, d88104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d87009, d88104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d87010 q = 0) : d88105 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d87010, d88105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d87010, d88105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d87011 q = 0) : d88106 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d87011, d88106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d87011, d88106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d87012 q = 0) : d88107 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d87012, d88107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d87012, d88107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d87013 q = 0) : d88108 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d87013, d88108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d87013, d88108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5181 (p : Pattern) (selected : d87019 p = 0) : d88114 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d87014 q = 0) : d88109 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d87014, d88109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5180 q selected
    | true =>
      simp only [d87014, d88109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d87015 q = 0) : d88110 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d87015, d88110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d87015, d88110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d87016 q = 0) : d88111 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d87016, d88111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d87016, d88111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d87017 q = 0) : d88112 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d87017, d88112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d87017, d88112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d87018 q = 0) : d88113 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d87018, d88113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d87018, d88113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d87019 q = 0) : d88114 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d87019, d88114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d87019, d88114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5182 (p : Pattern) (selected : d87025 p = 0) : d88120 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d87020 q = 0) : d88115 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d87020, d88115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5181 q selected
    | true =>
      simp only [d87020, d88115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d87021 q = 0) : d88116 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d87021, d88116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d87021, d88116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d87022 q = 0) : d88117 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d87022, d88117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d87022, d88117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d87023 q = 0) : d88118 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d87023, d88118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d87023, d88118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d87024 q = 0) : d88119 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d87024, d88119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d87024, d88119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d87025 q = 0) : d88120 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d87025, d88120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d87025, d88120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5183 (p : Pattern) (selected : d87031 p = 0) : d88126 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d87026 q = 0) : d88121 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d87026, d88121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5182 q selected
    | true =>
      simp only [d87026, d88121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d87027 q = 0) : d88122 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d87027, d88122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d87027, d88122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d87028 q = 0) : d88123 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d87028, d88123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d87028, d88123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d87029 q = 0) : d88124 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d87029, d88124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d87029, d88124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d87030 q = 0) : d88125 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d87030, d88125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d87030, d88125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d87031 q = 0) : d88126 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d87031, d88126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d87031, d88126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5184 (p : Pattern) (selected : d87037 p = 0) : d88132 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d87032 q = 0) : d88127 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d87032, d88127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5183 q selected
    | true =>
      simp only [d87032, d88127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d87033 q = 0) : d88128 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d87033, d88128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d87033, d88128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d87034 q = 0) : d88129 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d87034, d88129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d87034, d88129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d87035 q = 0) : d88130 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d87035, d88130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d87035, d88130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d87036 q = 0) : d88131 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d87036, d88131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d87036, d88131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d87037 q = 0) : d88132 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d87037, d88132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d87037, d88132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5185 (p : Pattern) (selected : d87043 p = 0) : d88138 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d87038 q = 0) : d88133 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d87038, d88133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5184 q selected
    | true =>
      simp only [d87038, d88133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d87039 q = 0) : d88134 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d87039, d88134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d87039, d88134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d87040 q = 0) : d88135 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d87040, d88135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d87040, d88135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d87041 q = 0) : d88136 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d87041, d88136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d87041, d88136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d87042 q = 0) : d88137 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d87042, d88137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d87042, d88137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d87043 q = 0) : d88138 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d87043, d88138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d87043, d88138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5186 (p : Pattern) (selected : d85826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d85823 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2 q selected
  have h2 (q : Pattern) (selected : d85824 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85825 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85826 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d85826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5187 (p : Pattern) (selected : d85832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d85827 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5186 q selected
    | true =>
      simp only [d85827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85828 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85829 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85830 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85831 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d85832 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5188 (p : Pattern) (selected : d85838 p = 1) : d89312 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d85805 q = 1) : d85805 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d85811 q = 1) : d85811 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d85822 q = 1) : d85822 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d85833 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5187 q selected
    | true =>
      simp only [d85833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85834 q = 1) : d89308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85834, d89308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85834, d89308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85736 q = 1) : d85736 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d85835 q = 1) : d89309 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85835, d89309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85835, d89309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d85836 q = 1) : d89310 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85836, d89310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85836, d89310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d85837 q = 1) : d89311 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85837, d89311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85837, d89311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d85838 q = 1) : d89312 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85838, d89312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85838, d89312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro5189 (p : Pattern) (selected : d85850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d85827 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5186 q selected
    | true =>
      simp only [d85827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85828 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85829 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85830 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85831 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d85850 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5190 (p : Pattern) (selected : d85856 p = 1) : d89317 p = 1 := by
  have h0 (q : Pattern) (selected : d85805 q = 1) : d85805 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d85811 q = 1) : d85811 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d85822 q = 1) : d85822 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d85833 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5187 q selected
    | true =>
      simp only [d85833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85834 q = 1) : d89308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85834, d89308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85834, d89308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85736 q = 1) : d85736 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d85835 q = 1) : d89309 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85835, d89309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85835, d89309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d85836 q = 1) : d89310 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85836, d89310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85836, d89310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d85837 q = 1) : d89311 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85837, d89311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85837, d89311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d85843 q = 1) : d85843 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d85847 q = 1) : d85847 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d85849 q = 1) : d85849 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d85851 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5189 q selected
    | true =>
      simp only [d85851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d85852 q = 1) : d89313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85852, d89313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d85852, d89313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d85743 q = 1) : d85743 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d85853 q = 1) : d89314 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85853, d89314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d85853, d89314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d85854 q = 1) : d89315 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85854, d89315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d85854, d89315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d85855 q = 1) : d89316 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85855, d89316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d85855, d89316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d85856 q = 1) : d89317 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85856, d89317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d85856, d89317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro5191 (p : Pattern) (selected : d85865 p = 1) : d89324 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d85849 q = 1) : d85849 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d85851 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5189 q selected
    | true =>
      simp only [d85851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d85852 q = 1) : d89313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85852, d89313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85852, d89313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d85743 q = 1) : d85743 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d85853 q = 1) : d89314 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85853, d89314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85853, d89314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85863 q = 1) : d89322 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85863, d89322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85863, d89322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d85864 q = 1) : d89323 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85864, d89323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85864, d89323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d85865 q = 1) : d89324 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85865, d89324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85865, d89324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5192 (p : Pattern) (selected : d85885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d85882 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9 q selected
  have h2 (q : Pattern) (selected : d85883 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85884 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85885 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d85885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5193 (p : Pattern) (selected : d85891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d85886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5192 q selected
    | true =>
      simp only [d85886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85888 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85889 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85890 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d85891 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5194 (p : Pattern) (selected : d85897 p = 1) : d89334 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d85881 q = 1) : d85881 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d85892 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5193 q selected
    | true =>
      simp only [d85892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d85893 q = 1) : d89330 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85893, d89330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85893, d89330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d85769 q = 1) : d85769 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d85894 q = 1) : d89331 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85894, d89331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85894, d89331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85895 q = 1) : d89332 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85895, d89332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85895, d89332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d85896 q = 1) : d89333 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85896, d89333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85896, d89333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d85897 q = 1) : d89334 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85897, d89334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85897, d89334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5195 (p : Pattern) (selected : d85903 p = 1) : d89340 p = 1 := by
  have h0 (q : Pattern) (selected : d85799 q = 1) : d85799 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d85857 q = 1) : d89318 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85857, d89318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5188 q selected
    | true =>
      simp only [d85857, d89318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5190 q selected
  have h2 (q : Pattern) (selected : d85859 q = 1) : d85859 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d85860 q = 1) : d89319 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85860, d89319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85860, d89319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d85861 q = 1) : d89320 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85861, d89320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85861, d89320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85862 q = 1) : d89321 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85862, d89321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85862, d89321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d85866 q = 1) : d89325 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85866, d89325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85866, d89325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5191 q selected
  have h8 (q : Pattern) (selected : d85867 q = 1) : d89326 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85867, d89326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d85867, d89326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d85868 q = 1) : d89327 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85868, d89327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d85868, d89327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d85869 q = 1) : d89328 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85869, d89328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d85869, d89328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d85870 q = 1) : d89329 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85870, d89329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d85870, d89329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d85898 q = 1) : d89335 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85898, d89335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85898, d89335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5194 q selected
  have h13 (q : Pattern) (selected : d85899 q = 1) : d89336 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85899, d89336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d85899, d89336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d85900 q = 1) : d89337 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85900, d89337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d85900, d89337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d85901 q = 1) : d89338 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85901, d89338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d85901, d89338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d85902 q = 1) : d89339 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85902, d89339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d85902, d89339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d85903 q = 1) : d89340 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85903, d89340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d85903, d89340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro5196 (p : Pattern) (selected : d85909 p = 1) : d89346 p = 1 := by
  have h0 (q : Pattern) (selected : d85784 q = 1) : d85784 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d85904 q = 1) : d89341 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85904, d89341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85904, d89341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5195 q selected
  have h3 (q : Pattern) (selected : d85905 q = 1) : d89342 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85905, d89342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85905, d89342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d85906 q = 1) : d89343 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85906, d89343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85906, d89343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85907 q = 1) : d89344 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85907, d89344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85907, d89344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85908 q = 1) : d89345 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85908, d89345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85908, d89345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d85909 q = 1) : d89346 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85909, d89346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85909, d89346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro5197 (p : Pattern) (selected : d85951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d85948 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16 q selected
  have h2 (q : Pattern) (selected : d85949 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85823 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2 q selected
  have h4 (q : Pattern) (selected : d85824 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85950 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85951 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d85951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5198 (p : Pattern) (selected : d85957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d85952 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5197 q selected
    | true =>
      simp only [d85952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85953 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85827 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5186 q selected
    | true =>
      simp only [d85827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85828 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85954 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85955 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d85956 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d85956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d85957 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5199 (p : Pattern) (selected : d85969 p = 1) : d89351 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d85930 q = 1) : d85930 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d85936 q = 1) : d85936 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d85947 q = 1) : d85947 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d85958 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5198 q selected
    | true =>
      simp only [d85958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5187 q selected
  have h5 (q : Pattern) (selected : d85959 q = 1) : d89347 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85959, d89347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85959, d89347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85965 q = 1) : d85965 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d85966 q = 1) : d89348 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85966, d89348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85966, d89348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d85967 q = 1) : d89349 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85967, d89349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85967, d89349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d85968 q = 1) : d89350 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85968, d89350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85968, d89350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d85969 q = 1) : d89351 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85969, d89351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85969, d89351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro5200 (p : Pattern) (selected : d85981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d85952 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5197 q selected
    | true =>
      simp only [d85952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85953 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85827 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5186 q selected
    | true =>
      simp only [d85827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85828 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85954 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85955 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d85956 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d85956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d85981 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d85981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5201 (p : Pattern) (selected : d85990 p = 1) : d89356 p = 1 := by
  have h0 (q : Pattern) (selected : d85930 q = 1) : d85930 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d85936 q = 1) : d85936 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d85947 q = 1) : d85947 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d85958 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5198 q selected
    | true =>
      simp only [d85958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5187 q selected
  have h4 (q : Pattern) (selected : d85959 q = 1) : d89347 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85959, d89347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85959, d89347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85965 q = 1) : d85965 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d85966 q = 1) : d89348 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85966, d89348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85966, d89348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d85967 q = 1) : d89349 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85967, d89349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85967, d89349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d85968 q = 1) : d89350 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85968, d89350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85968, d89350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d85974 q = 1) : d85974 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d85978 q = 1) : d85978 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d85980 q = 1) : d85980 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d85982 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5200 q selected
    | true =>
      simp only [d85982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5189 q selected
  have h13 (q : Pattern) (selected : d85983 q = 1) : d89352 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85983, d89352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d85983, d89352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d85986 q = 1) : d85986 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d85987 q = 1) : d89353 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85987, d89353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d85987, d89353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d85988 q = 1) : d89354 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85988, d89354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d85988, d89354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d85989 q = 1) : d89355 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85989, d89355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d85989, d89355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d85990 q = 1) : d89356 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85990, d89356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d85990, d89356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro5202 (p : Pattern) (selected : d85999 p = 1) : d89363 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d85980 q = 1) : d85980 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d85982 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5200 q selected
    | true =>
      simp only [d85982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5189 q selected
  have h3 (q : Pattern) (selected : d85983 q = 1) : d89352 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85983, d89352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85983, d89352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d85986 q = 1) : d85986 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d85987 q = 1) : d89353 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85987, d89353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85987, d89353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85997 q = 1) : d89361 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85997, d89361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85997, d89361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d85998 q = 1) : d89362 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85998, d89362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85998, d89362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d85999 q = 1) : d89363 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85999, d89363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85999, d89363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5203 (p : Pattern) (selected : d86021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86018 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23 q selected
  have h2 (q : Pattern) (selected : d86019 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85882 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9 q selected
  have h4 (q : Pattern) (selected : d85883 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86020 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86021 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5204 (p : Pattern) (selected : d86027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86022 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5203 q selected
    | true =>
      simp only [d86022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86023 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5192 q selected
    | true =>
      simp only [d85886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86024 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86025 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86026 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86027 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5205 (p : Pattern) (selected : d86039 p = 1) : d89373 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86017 q = 1) : d86017 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d86028 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5204 q selected
    | true =>
      simp only [d86028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5193 q selected
  have h3 (q : Pattern) (selected : d86029 q = 1) : d89369 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86029, d89369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86029, d89369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86035 q = 1) : d86035 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d86036 q = 1) : d89370 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86036, d89370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86036, d89370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86037 q = 1) : d89371 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86037, d89371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86037, d89371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86038 q = 1) : d89372 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86038, d89372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86038, d89372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86039 q = 1) : d89373 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86039, d89373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86039, d89373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5206 (p : Pattern) (selected : d86051 p = 1) : d89379 p = 1 := by
  have h0 (q : Pattern) (selected : d85924 q = 1) : d85924 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d85991 q = 1) : d89357 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85991, d89357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5199 q selected
    | true =>
      simp only [d85991, d89357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5201 q selected
  have h2 (q : Pattern) (selected : d85993 q = 1) : d85993 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d85994 q = 1) : d89358 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85994, d89358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85994, d89358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d85995 q = 1) : d89359 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85995, d89359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85995, d89359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85996 q = 1) : d89360 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85996, d89360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85996, d89360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86000 q = 1) : d89364 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86000, d89364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86000, d89364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5202 q selected
  have h8 (q : Pattern) (selected : d86002 q = 1) : d86002 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d86003 q = 1) : d89365 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86003, d89365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86003, d89365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86004 q = 1) : d89366 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86004, d89366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d86004, d89366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d86005 q = 1) : d89367 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86005, d89367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86005, d89367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d86006 q = 1) : d89368 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d86006, d89368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86006, d89368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d86040 q = 1) : d89374 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86040, d89374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86040, d89374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5205 q selected
  have h14 (q : Pattern) (selected : d86046 q = 1) : d86046 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d86047 q = 1) : d89375 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86047, d89375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d86047, d89375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d86048 q = 1) : d89376 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86048, d89376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d86048, d89376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d86049 q = 1) : d89377 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86049, d89377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d86049, d89377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d86050 q = 1) : d89378 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d86050, d89378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d86050, d89378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d86051 q = 1) : d89379 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d86051, d89379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d86051, d89379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro5207 (p : Pattern) (selected : d86057 p = 1) : d89385 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86052 q = 1) : d89380 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d86052, d89380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86052, d89380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5206 q selected
  have h2 (q : Pattern) (selected : d86053 q = 1) : d89381 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d86053, d89381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86053, d89381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86054 q = 1) : d89382 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d86054, d89382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86054, d89382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86055 q = 1) : d89383 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d86055, d89383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86055, d89383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86056 q = 1) : d89384 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d86056, d89384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86056, d89384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86057 q = 1) : d89385 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d86057, d89385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86057, d89385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5208 (p : Pattern) (selected : d86131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86126 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro54 q selected
  have h2 (q : Pattern) (selected : d86127 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86128 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro55 q selected
  have h4 (q : Pattern) (selected : d86129 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86130 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86131 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5209 (p : Pattern) (selected : d86135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86128 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro55 q selected
  have h2 (q : Pattern) (selected : d86129 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86134 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86135 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5210 (p : Pattern) (selected : d86141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86132 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5208 q selected
    | true =>
      simp only [d86132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86133 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5209 q selected
    | true =>
      simp only [d86136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86138 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86139 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86140 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86141 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5211 (p : Pattern) (selected : d86145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5209 q selected
    | true =>
      simp only [d86136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86142 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86143 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86144 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86145 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5212 (p : Pattern) (selected : d86157 p = 1) : d89391 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86105 q = 1) : d86105 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d86114 q = 1) : d86114 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d86125 q = 1) : d86125 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d86146 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5210 q selected
    | true =>
      simp only [d86146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5211 q selected
  have h5 (q : Pattern) (selected : d86147 q = 1) : d89387 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86147, d89387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86147, d89387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86153 q = 1) : d86153 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d86154 q = 1) : d89388 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86154, d89388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86154, d89388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86155 q = 1) : d89389 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86155, d89389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86155, d89389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86156 q = 1) : d89390 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86156, d89390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86156, d89390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86157 q = 1) : d89391 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86157, d89391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86157, d89391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro5213 (p : Pattern) (selected : d86171 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86132 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5208 q selected
    | true =>
      simp only [d86132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86133 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5209 q selected
    | true =>
      simp only [d86136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86138 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86139 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86140 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86171 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5214 (p : Pattern) (selected : d86172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5209 q selected
    | true =>
      simp only [d86136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86142 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86143 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86144 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86172 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5215 (p : Pattern) (selected : d86181 p = 1) : d89396 p = 1 := by
  have h0 (q : Pattern) (selected : d86105 q = 1) : d86105 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86114 q = 1) : d86114 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d86125 q = 1) : d86125 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d86146 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5210 q selected
    | true =>
      simp only [d86146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5211 q selected
  have h4 (q : Pattern) (selected : d86147 q = 1) : d89387 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86147, d89387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86147, d89387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86153 q = 1) : d86153 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d86154 q = 1) : d89388 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86154, d89388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86154, d89388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86155 q = 1) : d89389 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86155, d89389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86155, d89389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86156 q = 1) : d89390 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86156, d89390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86156, d89390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86163 q = 1) : d86163 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d86168 q = 1) : d86168 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d86170 q = 1) : d86170 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d86173 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5213 q selected
    | true =>
      simp only [d86173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5214 q selected
  have h13 (q : Pattern) (selected : d86174 q = 1) : d89392 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86174, d89392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d86174, d89392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d86177 q = 1) : d86177 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d86178 q = 1) : d89393 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86178, d89393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d86178, d89393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d86179 q = 1) : d89394 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86179, d89394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86179, d89394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d86180 q = 1) : d89395 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86180, d89395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d86180, d89395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d86181 q = 1) : d89396 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86181, d89396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d86181, d89396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro5216 (p : Pattern) (selected : d86201 p = 1) : d89403 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86170 q = 1) : d86170 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d86173 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5213 q selected
    | true =>
      simp only [d86173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5214 q selected
  have h3 (q : Pattern) (selected : d86174 q = 1) : d89392 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86174, d89392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86174, d89392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86177 q = 1) : d86177 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d86178 q = 1) : d89393 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86178, d89393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86178, d89393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86199 q = 1) : d89401 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86199, d89401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86199, d89401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86200 q = 1) : d89402 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86200, d89402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86200, d89402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86201 q = 1) : d89403 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86201, d89403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86201, d89403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5217 (p : Pattern) (selected : d86241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86236 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro66 q selected
  have h2 (q : Pattern) (selected : d86237 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86238 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro67 q selected
  have h4 (q : Pattern) (selected : d86239 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86240 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86241 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5218 (p : Pattern) (selected : d86245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86238 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro67 q selected
  have h2 (q : Pattern) (selected : d86239 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86244 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86245 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5219 (p : Pattern) (selected : d86251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86242 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5217 q selected
    | true =>
      simp only [d86242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86243 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86246 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5218 q selected
    | true =>
      simp only [d86246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86247 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86248 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86249 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86250 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86251 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5220 (p : Pattern) (selected : d86255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86246 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5218 q selected
    | true =>
      simp only [d86246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86247 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86252 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86253 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86254 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86255 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5221 (p : Pattern) (selected : d86267 p = 1) : d89413 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86235 q = 1) : d86235 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d86256 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5219 q selected
    | true =>
      simp only [d86256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5220 q selected
  have h3 (q : Pattern) (selected : d86257 q = 1) : d89409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86257, d89409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86257, d89409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86263 q = 1) : d86263 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d86264 q = 1) : d89410 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86264, d89410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86264, d89410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86265 q = 1) : d89411 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86265, d89411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86265, d89411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86266 q = 1) : d89412 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86266, d89412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86266, d89412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86267 q = 1) : d89413 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86267, d89413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86267, d89413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5222 (p : Pattern) (selected : d86284 p = 1) : d89419 p = 1 := by
  have h0 (q : Pattern) (selected : d86097 q = 1) : d86097 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86182 q = 1) : d89397 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86182, d89397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5212 q selected
    | true =>
      simp only [d86182, d89397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5215 q selected
  have h2 (q : Pattern) (selected : d86195 q = 1) : d86195 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d86196 q = 1) : d89398 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86196, d89398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86196, d89398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d86197 q = 1) : d89399 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86197, d89399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86197, d89399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86198 q = 1) : d89400 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86198, d89400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86198, d89400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86202 q = 1) : d89404 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86202, d89404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86202, d89404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5216 q selected
  have h8 (q : Pattern) (selected : d86204 q = 1) : d86204 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d86205 q = 1) : d89405 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86205, d89405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86205, d89405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86206 q = 1) : d89406 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86206, d89406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d86206, d89406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d86207 q = 1) : d89407 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86207, d89407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86207, d89407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d86208 q = 1) : d89408 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d86208, d89408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86208, d89408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d86268 q = 1) : d89414 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86268, d89414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86268, d89414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5221 q selected
  have h14 (q : Pattern) (selected : d86279 q = 1) : d86279 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d86280 q = 1) : d89415 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86280, d89415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d86280, d89415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d86281 q = 1) : d89416 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86281, d89416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d86281, d89416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d86282 q = 1) : d89417 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86282, d89417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d86282, d89417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d86283 q = 1) : d89418 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d86283, d89418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d86283, d89418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d86284 q = 1) : d89419 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d86284, d89419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d86284, d89419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro5223 (p : Pattern) (selected : d86290 p = 1) : d89425 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86285 q = 1) : d89420 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d86285, d89420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86285, d89420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5222 q selected
  have h2 (q : Pattern) (selected : d86286 q = 1) : d89421 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d86286, d89421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86286, d89421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86287 q = 1) : d89422 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d86287, d89422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86287, d89422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86288 q = 1) : d89423 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d86288, d89423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86288, d89423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86289 q = 1) : d89424 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d86289, d89424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86289, d89424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86290 q = 1) : d89425 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d86290, d89425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86290, d89425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5224 (p : Pattern) (selected : d86365 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86360 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro83 q selected
  have h2 (q : Pattern) (selected : d86361 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86362 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro85 q selected
  have h4 (q : Pattern) (selected : d86363 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86364 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86365 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5225 (p : Pattern) (selected : d86369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86362 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro85 q selected
  have h2 (q : Pattern) (selected : d86363 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86368 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86369 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5226 (p : Pattern) (selected : d86375 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86366 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5224 q selected
    | true =>
      simp only [d86366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86367 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86370 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5225 q selected
    | true =>
      simp only [d86370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86371 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86372 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86373 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86374 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86375 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5227 (p : Pattern) (selected : d86379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86370 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5225 q selected
    | true =>
      simp only [d86370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86371 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86376 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86377 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86378 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86379 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5228 (p : Pattern) (selected : d86391 p = 1) : d89432 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86339 q = 1) : d86339 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d86348 q = 1) : d86348 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d86359 q = 1) : d86359 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d86380 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5226 q selected
    | true =>
      simp only [d86380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5227 q selected
  have h5 (q : Pattern) (selected : d86381 q = 1) : d89428 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86381, d89428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86381, d89428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86387 q = 1) : d86387 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d86388 q = 1) : d89429 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86388, d89429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86388, d89429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86389 q = 1) : d89430 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86389, d89430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86389, d89430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86390 q = 1) : d89431 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86390, d89431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86390, d89431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86391 q = 1) : d89432 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86391, d89432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86391, d89432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro5229 (p : Pattern) (selected : d86405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86366 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5224 q selected
    | true =>
      simp only [d86366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86367 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86370 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5225 q selected
    | true =>
      simp only [d86370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86371 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86372 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86373 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86374 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86405 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5230 (p : Pattern) (selected : d86406 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86370 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5225 q selected
    | true =>
      simp only [d86370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86371 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86376 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86377 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86378 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86406 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5231 (p : Pattern) (selected : d86415 p = 1) : d89437 p = 1 := by
  have h0 (q : Pattern) (selected : d86339 q = 1) : d86339 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86348 q = 1) : d86348 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d86359 q = 1) : d86359 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d86380 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5226 q selected
    | true =>
      simp only [d86380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5227 q selected
  have h4 (q : Pattern) (selected : d86381 q = 1) : d89428 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86381, d89428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86381, d89428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86387 q = 1) : d86387 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d86388 q = 1) : d89429 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86388, d89429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86388, d89429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86389 q = 1) : d89430 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86389, d89430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86389, d89430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86390 q = 1) : d89431 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86390, d89431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86390, d89431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86397 q = 1) : d86397 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d86402 q = 1) : d86402 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d86404 q = 1) : d86404 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d86407 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5229 q selected
    | true =>
      simp only [d86407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5230 q selected
  have h13 (q : Pattern) (selected : d86408 q = 1) : d89433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86408, d89433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d86408, d89433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d86411 q = 1) : d86411 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d86412 q = 1) : d89434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86412, d89434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d86412, d89434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d86413 q = 1) : d89435 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86413, d89435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86413, d89435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d86414 q = 1) : d89436 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86414, d89436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d86414, d89436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d86415 q = 1) : d89437 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86415, d89437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d86415, d89437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro5232 (p : Pattern) (selected : d86435 p = 1) : d89444 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86404 q = 1) : d86404 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d86407 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5229 q selected
    | true =>
      simp only [d86407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5230 q selected
  have h3 (q : Pattern) (selected : d86408 q = 1) : d89433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86408, d89433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86408, d89433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86411 q = 1) : d86411 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d86412 q = 1) : d89434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86412, d89434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86412, d89434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86433 q = 1) : d89442 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86433, d89442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86433, d89442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86434 q = 1) : d89443 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86434, d89443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86434, d89443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86435 q = 1) : d89444 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86435, d89444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86435, d89444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5233 (p : Pattern) (selected : d86475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86470 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro96 q selected
  have h2 (q : Pattern) (selected : d86471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86472 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro97 q selected
  have h4 (q : Pattern) (selected : d86473 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86474 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86475 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5234 (p : Pattern) (selected : d86479 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86472 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro97 q selected
  have h2 (q : Pattern) (selected : d86473 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86478 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86479 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5235 (p : Pattern) (selected : d86485 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86476 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5233 q selected
    | true =>
      simp only [d86476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86477 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86480 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5234 q selected
    | true =>
      simp only [d86480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86481 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86482 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86483 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86484 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86485 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5236 (p : Pattern) (selected : d86489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86480 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5234 q selected
    | true =>
      simp only [d86480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86481 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86486 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86488 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86489 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5237 (p : Pattern) (selected : d86501 p = 1) : d89454 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86469 q = 1) : d86469 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d86490 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5235 q selected
    | true =>
      simp only [d86490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5236 q selected
  have h3 (q : Pattern) (selected : d86491 q = 1) : d89450 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86491, d89450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86491, d89450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86497 q = 1) : d86497 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d86498 q = 1) : d89451 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86498, d89451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86498, d89451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86499 q = 1) : d89452 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86499, d89452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86499, d89452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86500 q = 1) : d89453 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86500, d89453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86500, d89453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86501 q = 1) : d89454 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86501, d89454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86501, d89454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5238 (p : Pattern) (selected : d86518 p = 1) : d89460 p = 1 := by
  have h0 (q : Pattern) (selected : d86331 q = 1) : d86331 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86416 q = 1) : d89438 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86416, d89438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5228 q selected
    | true =>
      simp only [d86416, d89438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5231 q selected
  have h2 (q : Pattern) (selected : d86429 q = 1) : d86429 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d86430 q = 1) : d89439 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86430, d89439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86430, d89439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d86431 q = 1) : d89440 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86431, d89440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86431, d89440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86432 q = 1) : d89441 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86432, d89441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86432, d89441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86436 q = 1) : d89445 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86436, d89445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86436, d89445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5232 q selected
  have h8 (q : Pattern) (selected : d86438 q = 1) : d86438 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d86439 q = 1) : d89446 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86439, d89446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86439, d89446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86440 q = 1) : d89447 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86440, d89447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d86440, d89447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d86441 q = 1) : d89448 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86441, d89448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86441, d89448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d86442 q = 1) : d89449 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d86442, d89449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86442, d89449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d86502 q = 1) : d89455 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86502, d89455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86502, d89455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5237 q selected
  have h14 (q : Pattern) (selected : d86513 q = 1) : d86513 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d86514 q = 1) : d89456 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86514, d89456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d86514, d89456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d86515 q = 1) : d89457 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86515, d89457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d86515, d89457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d86516 q = 1) : d89458 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86516, d89458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d86516, d89458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d86517 q = 1) : d89459 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d86517, d89459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d86517, d89459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d86518 q = 1) : d89460 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d86518, d89460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d86518, d89460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro5239 (p : Pattern) (selected : d86524 p = 1) : d89466 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86519 q = 1) : d89461 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d86519, d89461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86519, d89461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5238 q selected
  have h2 (q : Pattern) (selected : d86520 q = 1) : d89462 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d86520, d89462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86520, d89462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86521 q = 1) : d89463 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d86521, d89463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86521, d89463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86522 q = 1) : d89464 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d86522, d89464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86522, d89464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86523 q = 1) : d89465 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d86523, d89465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86523, d89465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86524 q = 1) : d89466 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d86524, d89466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86524, d89466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5240 (p : Pattern) (selected : d86600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86595 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro119 q selected
  have h2 (q : Pattern) (selected : d86596 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86597 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro121 q selected
  have h4 (q : Pattern) (selected : d86598 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86599 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86600 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5241 (p : Pattern) (selected : d86604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86597 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro121 q selected
  have h2 (q : Pattern) (selected : d86598 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86603 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86604 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5242 (p : Pattern) (selected : d86610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86601 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5240 q selected
    | true =>
      simp only [d86601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86602 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86605 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5241 q selected
    | true =>
      simp only [d86605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86606 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86607 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86608 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86609 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86610 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5243 (p : Pattern) (selected : d86614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86605 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5241 q selected
    | true =>
      simp only [d86605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86606 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86611 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86612 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86613 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86614 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5244 (p : Pattern) (selected : d86626 p = 1) : d89474 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86574 q = 1) : d86574 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d86583 q = 1) : d86583 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d86594 q = 1) : d86594 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d86615 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5242 q selected
    | true =>
      simp only [d86615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5243 q selected
  have h5 (q : Pattern) (selected : d86616 q = 1) : d89470 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86616, d89470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86616, d89470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86622 q = 1) : d86622 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d86623 q = 1) : d89471 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86623, d89471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86623, d89471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86624 q = 1) : d89472 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86624, d89472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86624, d89472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86625 q = 1) : d89473 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86625, d89473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86625, d89473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86626 q = 1) : d89474 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86626, d89474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86626, d89474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro5245 (p : Pattern) (selected : d86640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86601 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5240 q selected
    | true =>
      simp only [d86601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86602 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86605 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5241 q selected
    | true =>
      simp only [d86605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86606 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86607 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86608 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86609 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86640 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5246 (p : Pattern) (selected : d86641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86605 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5241 q selected
    | true =>
      simp only [d86605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86606 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86611 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86612 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86613 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86641 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5247 (p : Pattern) (selected : d86650 p = 1) : d89479 p = 1 := by
  have h0 (q : Pattern) (selected : d86574 q = 1) : d86574 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86583 q = 1) : d86583 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d86594 q = 1) : d86594 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d86615 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5242 q selected
    | true =>
      simp only [d86615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5243 q selected
  have h4 (q : Pattern) (selected : d86616 q = 1) : d89470 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86616, d89470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86616, d89470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86622 q = 1) : d86622 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d86623 q = 1) : d89471 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86623, d89471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86623, d89471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86624 q = 1) : d89472 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86624, d89472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86624, d89472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86625 q = 1) : d89473 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86625, d89473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86625, d89473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86632 q = 1) : d86632 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d86637 q = 1) : d86637 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d86639 q = 1) : d86639 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d86642 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5245 q selected
    | true =>
      simp only [d86642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5246 q selected
  have h13 (q : Pattern) (selected : d86643 q = 1) : d89475 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86643, d89475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d86643, d89475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d86646 q = 1) : d86646 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d86647 q = 1) : d89476 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86647, d89476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d86647, d89476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d86648 q = 1) : d89477 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86648, d89477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86648, d89477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d86649 q = 1) : d89478 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86649, d89478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d86649, d89478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d86650 q = 1) : d89479 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86650, d89479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d86650, d89479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro5248 (p : Pattern) (selected : d86670 p = 1) : d89486 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86639 q = 1) : d86639 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d86642 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5245 q selected
    | true =>
      simp only [d86642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5246 q selected
  have h3 (q : Pattern) (selected : d86643 q = 1) : d89475 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86643, d89475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86643, d89475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86646 q = 1) : d86646 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d86647 q = 1) : d89476 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86647, d89476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86647, d89476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86668 q = 1) : d89484 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86668, d89484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86668, d89484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86669 q = 1) : d89485 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86669, d89485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86669, d89485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86670 q = 1) : d89486 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86670, d89486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86670, d89486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5249 (p : Pattern) (selected : d86710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86705 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro132 q selected
  have h2 (q : Pattern) (selected : d86706 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86707 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro133 q selected
  have h4 (q : Pattern) (selected : d86708 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86709 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86710 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
