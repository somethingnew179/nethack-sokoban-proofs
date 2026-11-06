import NetHack.Soko22Hazard87.EqIntroBlocks0153
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro38500 (p : Pattern) (selected : d46354 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46341 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38497 q selected
    | true =>
      simp only [d46341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46342 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46349 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38499 q selected
    | true =>
      simp only [d46349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46350 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46351 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46352 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46353 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46354 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38501 (p : Pattern) (selected : d46374 p = 2) : d46300 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46356 q = 2) : d46286 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46356, d46286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46356, d46286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38460 q selected
  have h2 (q : Pattern) (selected : d46109 q = 2) : d45916 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46109, d45916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38460 q selected
    | true =>
      simp only [d46109, d45916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46357 q = 2) : d46287 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46357, d46287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46357, d46287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46110 q = 2) : d45917 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46110, d45917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46110, d45917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46358 q = 2) : d46288 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46358, d46288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46358, d46288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46359 q = 2) : d46289 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46359, d46289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46359, d46289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46360 q = 2) : d46290 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46360, d46290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46360, d46290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38462 q selected
  have h8 (q : Pattern) (selected : d46125 q = 2) : d45928 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46125, d45928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38462 q selected
    | true =>
      simp only [d46125, d45928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46361 q = 2) : d46291 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46361, d46291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46361, d46291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46126 q = 2) : d45929 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46126, d45929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46126, d45929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46362 q = 2) : d46292 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46362, d46292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46362, d46292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d46363 q = 2) : d46293 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46363, d46293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46363, d46293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d46364 q = 2) : d46294 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46364, d46294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46364, d46294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46365 q = 2) : d46280 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46365, d46280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46365, d46280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38463 q selected
  have h15 (q : Pattern) (selected : d46136 q = 2) : d45937 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46136, d45937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38463 q selected
    | true =>
      simp only [d46136, d45937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d46366 q = 2) : d46281 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46366, d46281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d46366, d46281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d46137 q = 2) : d45938 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46137, d45938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d46137, d45938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d46367 q = 2) : d46282 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46367, d46282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d46367, d46282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d46368 q = 2) : d46283 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46368, d46283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d46368, d46283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d46369 q = 2) : d46295 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46369, d46295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46369, d46295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38464 q selected
  have h21 (q : Pattern) (selected : d46145 q = 2) : d45946 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46145, d45946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38464 q selected
    | true =>
      simp only [d46145, d45946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d46370 q = 2) : d46296 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46370, d46296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d46370, d46296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d46146 q = 2) : d45947 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46146, d45947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d46146, d45947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d46371 q = 2) : d46297 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46371, d46297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d46371, d46297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d46372 q = 2) : d46298 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46372, d46298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d46372, d46298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d46373 q = 2) : d46299 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46373, d46299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d46373, d46299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d46374 q = 2) : d46300 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46374, d46300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46374, d46300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro38502 (p : Pattern) (selected : d46385 p = 2) : d46324 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46375 q = 2) : d46315 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46375, d46315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46375, d46315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38466 q selected
  have h2 (q : Pattern) (selected : d46157 q = 2) : d45958 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46157, d45958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38466 q selected
    | true =>
      simp only [d46157, d45958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46376 q = 2) : d46316 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46376, d46316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46376, d46316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46158 q = 2) : d45959 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46158, d45959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46158, d45959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46377 q = 2) : d46317 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46377, d46317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46377, d46317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46378 q = 2) : d46318 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46378, d46318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46378, d46318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46379 q = 2) : d46319 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46379, d46319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46379, d46319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38467 q selected
  have h8 (q : Pattern) (selected : d46162 q = 2) : d45963 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46162, d45963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38467 q selected
    | true =>
      simp only [d46162, d45963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46380 q = 2) : d46320 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46380, d46320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46380, d46320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46163 q = 2) : d45964 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46163, d45964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46163, d45964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46381 q = 2) : d46321 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46381, d46321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46381, d46321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d46382 q = 2) : d46322 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46382, d46322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46382, d46322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d46383 q = 2) : d46323 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46383, d46323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46383, d46323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46369 q = 2) : d46295 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46369, d46295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46369, d46295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38464 q selected
  have h15 (q : Pattern) (selected : d46145 q = 2) : d45946 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46145, d45946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38464 q selected
    | true =>
      simp only [d46145, d45946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d46370 q = 2) : d46296 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46370, d46296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d46370, d46296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d46146 q = 2) : d45947 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46146, d45947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d46146, d45947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d46371 q = 2) : d46297 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46371, d46297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d46371, d46297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d46372 q = 2) : d46298 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46372, d46298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d46372, d46298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d46384 q = 2) : d46309 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46384, d46309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d46384, d46309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d46385 q = 2) : d46324 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46385, d46324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46385, d46324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro38503 (p : Pattern) (selected : d46390 p = 2) : d46329 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46379 q = 2) : d46319 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46379, d46319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46379, d46319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38467 q selected
  have h2 (q : Pattern) (selected : d46162 q = 2) : d45963 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46162, d45963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38467 q selected
    | true =>
      simp only [d46162, d45963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46380 q = 2) : d46320 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46380, d46320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46380, d46320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46163 q = 2) : d45964 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46163, d45964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46163, d45964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46381 q = 2) : d46321 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46381, d46321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46381, d46321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46382 q = 2) : d46322 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46382, d46322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46382, d46322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46389 q = 2) : d46328 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46389, d46328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46389, d46328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15073 q = 2) : d15019 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15073, d15019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15073, d15019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10581 q selected
  have h9 (q : Pattern) (selected : d9952 q = 2) : d9844 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, d9844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10581 q selected
    | true =>
      simp only [d9952, d9844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15074 q = 2) : d15020 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15074, d15020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15074, d15020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d9954 q = 2) : d9846 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9954, d9846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9954, d9846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15075 q = 2) : d15021 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15075, d15021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15075, d15021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15076 q = 2) : d15022 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15076, d15022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15076, d15022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15077 q = 2) : d15023 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15077, d15023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15077, d15023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46390 q = 2) : d46329 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46390, d46329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46390, d46329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38504 (p : Pattern) (selected : d46397 p = 2) : d46340 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46386 q = 2) : d46325 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46386, d46325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38501 q selected
    | true =>
      simp only [d46386, d46325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38502 q selected
  have h2 (q : Pattern) (selected : d46387 q = 2) : d46326 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46387, d46326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46387, d46326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46388 q = 2) : d46327 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46388, d46327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46388, d46327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46391 q = 2) : d46330 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46391, d46330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38502 q selected
    | true =>
      simp only [d46391, d46330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38503 q selected
  have h5 (q : Pattern) (selected : d46392 q = 2) : d46331 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46392, d46331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46392, d46331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46393 q = 2) : d46332 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46393, d46332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46393, d46332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46394 q = 2) : d46333 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46394, d46333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46394, d46333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46395 q = 2) : d46338 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46395, d46338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46395, d46338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46396 q = 2) : d46339 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46396, d46339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46396, d46339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46397 q = 2) : d46340 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46397, d46340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46397, d46340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38505 (p : Pattern) (selected : d46401 p = 2) : d46348 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46391 q = 2) : d46330 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46391, d46330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38502 q selected
    | true =>
      simp only [d46391, d46330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38503 q selected
  have h2 (q : Pattern) (selected : d46392 q = 2) : d46331 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46392, d46331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46392, d46331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46393 q = 2) : d46332 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46393, d46332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46393, d46332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46395 q = 2) : d46338 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46395, d46338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46395, d46338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46400 q = 2) : d46347 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46400, d46347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46400, d46347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46401 q = 2) : d46348 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46401, d46348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46401, d46348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38506 (p : Pattern) (selected : d46407 p = 2) : d46354 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46398 q = 2) : d46341 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46398, d46341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38504 q selected
    | true =>
      simp only [d46398, d46341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46399 q = 2) : d46342 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46399, d46342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46399, d46342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46402 q = 2) : d46349 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46402, d46349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38505 q selected
    | true =>
      simp only [d46402, d46349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46403 q = 2) : d46350 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46403, d46350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46403, d46350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46404 q = 2) : d46351 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46404, d46351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46404, d46351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46405 q = 2) : d46352 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46405, d46352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46405, d46352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46406 q = 2) : d46353 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46406, d46353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46406, d46353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46407 q = 2) : d46354 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46407, d46354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46407, d46354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38507 (p : Pattern) (selected : d46411 p = 2) : d46437 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46402 q = 2) : d46349 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46402, d46349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38505 q selected
    | true =>
      simp only [d46402, d46349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46403 q = 2) : d46350 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46403, d46350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46403, d46350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46408 q = 2) : d46434 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46408, d46434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46408, d46434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46409 q = 2) : d46435 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46409, d46435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46409, d46435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46410 q = 2) : d46436 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46410, d46436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46410, d46436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46411 q = 2) : d46437 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46411, d46437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46411, d46437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38508 (p : Pattern) (selected : d46414 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46319 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38434 q selected
  have h2 (q : Pattern) (selected : d45963 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38434 q selected
    | true =>
      simp only [d45963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46320 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45964 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46321 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46322 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46328 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46414 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38509 (p : Pattern) (selected : d46420 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46325 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38492 q selected
    | true =>
      simp only [d46325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38494 q selected
  have h2 (q : Pattern) (selected : d46326 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46327 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46330 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38494 q selected
    | true =>
      simp only [d46330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38495 q selected
  have h5 (q : Pattern) (selected : d46331 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46332 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46333 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46415 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38494 q selected
    | true =>
      simp only [d46415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38508 q selected
  have h9 (q : Pattern) (selected : d46416 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46417 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46418 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d46419 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46420 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro38510 (p : Pattern) (selected : d46426 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46421 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38509 q selected
    | true =>
      simp only [d46421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46422 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46423 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46424 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46425 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46426 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38511 (p : Pattern) (selected : d46432 p = 2) : d367694 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46355 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38498 q selected
    | true =>
      simp only [d46355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38500 q selected
  have h2 (q : Pattern) (selected : d46412 q = 2) : d367689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46412, d367689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38506 q selected
    | true =>
      simp only [d46412, d367689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38507 q selected
  have h3 (q : Pattern) (selected : d46413 q = 2) : d367690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46413, d367690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46413, d367690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46427 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38510 q selected
    | true =>
      simp only [d46427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46428 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46429 q = 2) : d367691 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46429, d367691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46429, d367691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46430 q = 2) : d367692 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46430, d367692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46430, d367692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46431 q = 2) : d367693 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46431, d367693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46431, d367693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46432 q = 2) : d367694 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46432, d367694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46432, d367694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38512 (p : Pattern) (selected : d46437 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46349 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38499 q selected
    | true =>
      simp only [d46349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46350 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46434 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46435 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46436 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46437 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38513 (p : Pattern) (selected : d46443 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46438 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38512 q selected
    | true =>
      simp only [d46438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46439 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46440 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46441 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46442 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46443 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38514 (p : Pattern) (selected : d46449 p = 2) : d367700 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46002 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38441 q selected
  have h2 (q : Pattern) (selected : d46003 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46012 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38441 q selected
    | true =>
      simp only [d46012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38444 q selected
  have h4 (q : Pattern) (selected : d46013 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46014 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46240 q = 2) : d46012 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46240, d46012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38477 q selected
    | true =>
      simp only [d46240, d46012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38486 q selected
  have h7 (q : Pattern) (selected : d46253 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38487 q selected
    | true =>
      simp only [d46253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38488 q selected
  have h8 (q : Pattern) (selected : d46254 q = 2) : d46013 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46254, d46013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46254, d46013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46255 q = 2) : d367681 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46255, d367681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46255, d367681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46256 q = 2) : d367682 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d46256, d367682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46256, d367682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46260 q = 2) : d367684 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46260, d367684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46260, d367684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38489 q selected
  have h12 (q : Pattern) (selected : d46262 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38490 q selected
  have h13 (q : Pattern) (selected : d46263 q = 2) : d367685 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46263, d367685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46263, d367685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46264 q = 2) : d367686 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46264, d367686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46264, d367686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46265 q = 2) : d367687 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d46265, d367687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d46265, d367687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d46266 q = 2) : d367688 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d46266, d367688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46266, d367688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d46433 q = 2) : d367695 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46433, d367695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46433, d367695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38511 q selected
  have h18 (q : Pattern) (selected : d46444 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38513 q selected
  have h19 (q : Pattern) (selected : d46445 q = 2) : d367696 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46445, d367696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d46445, d367696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d46446 q = 2) : d367697 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46446, d367697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d46446, d367697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d46447 q = 2) : d367698 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d46447, d367698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d46447, d367698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d46448 q = 2) : d367699 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d46448, d367699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d46448, d367699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d46449 q = 2) : d367700 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d46449, d367700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d46449, d367700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro38515 (p : Pattern) (selected : d46455 p = 2) : d367706 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46450 q = 2) : d367701 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d46450, d367701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46450, d367701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38514 q selected
  have h2 (q : Pattern) (selected : d46451 q = 2) : d367702 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d46451, d367702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46451, d367702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46452 q = 2) : d367703 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d46452, d367703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46452, d367703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46453 q = 2) : d367704 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d46453, d367704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46453, d367704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46454 q = 2) : d367705 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d46454, d367705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46454, d367705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46455 q = 2) : d367706 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d46455, d367706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46455, d367706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38516 (p : Pattern) (selected : d46460 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1 q = 2) : d0 q = 1 := by
    change (1 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d13 q = 2) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14 q = 2) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1084 q = 2) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44996 q = 2) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d44996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46459 q = 2) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46460 q = 2) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro38517 (p : Pattern) (selected : d46466 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46461 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38516 q selected
  have h2 (q : Pattern) (selected : d32155 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10556 q selected
  have h3 (q : Pattern) (selected : d46462 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46463 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46464 q = 2) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46465 q = 2) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46466 q = 2) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro38518 (p : Pattern) (selected : d46473 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1 q = 2) : d0 q = 1 := by
    change (1 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d13 q = 2) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14 q = 2) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15 q = 2) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45587 q = 2) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d45587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46472 q = 2) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46473 q = 2) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro38519 (p : Pattern) (selected : d46482 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46461 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38516 q selected
  have h2 (q : Pattern) (selected : d32155 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10556 q selected
  have h3 (q : Pattern) (selected : d46462 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46463 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46464 q = 2) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46465 q = 2) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46474 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38518 q selected
  have h8 (q : Pattern) (selected : d1115 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro644 q selected
  have h9 (q : Pattern) (selected : d46475 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46476 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46477 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38518 q selected
    | true =>
      simp only [d46477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d19 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro644 q selected
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d46478 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46479 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46480 q = 2) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d46481 q = 2) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d46481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d46482 q = 2) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro38520 (p : Pattern) (selected : d46488 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46467 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38517 q selected
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46468 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46469 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46470 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46471 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46483 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38519 q selected
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46484 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46485 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46486 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46487 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46488 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38521 (p : Pattern) (selected : d46490 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46467 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38517 q selected
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46468 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46469 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46470 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46483 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38519 q selected
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46484 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46485 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46486 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46487 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46489 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46490 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38522 (p : Pattern) (selected : d46494 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46474 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38518 q selected
  have h2 (q : Pattern) (selected : d1115 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro644 q selected
  have h3 (q : Pattern) (selected : d46475 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46476 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46477 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38518 q selected
    | true =>
      simp only [d46477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d19 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro644 q selected
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46478 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46479 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46480 q = 2) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46481 q = 2) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46494 q = 2) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h11 p selected
theorem eqIntro38523 (p : Pattern) (selected : d46500 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46483 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38519 q selected
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46484 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46485 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46486 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46489 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46495 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38522 q selected
    | true =>
      simp only [d46495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46496 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46497 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46498 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46499 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46500 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38524 (p : Pattern) (selected : d46507 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46491 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38520 q selected
    | true =>
      simp only [d46491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38521 q selected
  have h2 (q : Pattern) (selected : d46492 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46493 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46501 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38521 q selected
    | true =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38523 q selected
  have h5 (q : Pattern) (selected : d46502 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46503 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46504 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46505 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46506 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46507 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38525 (p : Pattern) (selected : d46511 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46501 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38521 q selected
    | true =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38523 q selected
  have h2 (q : Pattern) (selected : d46502 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46503 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46505 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46510 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46511 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38526 (p : Pattern) (selected : d46517 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46508 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38524 q selected
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46509 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46512 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38525 q selected
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46513 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46514 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46515 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46516 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46517 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38527 (p : Pattern) (selected : d46521 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46512 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38525 q selected
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46513 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46518 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46519 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46520 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46521 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38528 (p : Pattern) (selected : d46527 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46522 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38526 q selected
    | true =>
      simp only [d46522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38527 q selected
  have h2 (q : Pattern) (selected : d46523 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46524 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46525 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46526 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46527 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38529 (p : Pattern) (selected : d46530 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46508 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38524 q selected
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46509 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46512 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38525 q selected
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46513 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46514 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46515 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46516 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46530 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38530 (p : Pattern) (selected : d46531 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46512 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38525 q selected
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46513 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46518 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46519 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46520 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46531 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38531 (p : Pattern) (selected : d46537 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46522 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38526 q selected
    | true =>
      simp only [d46522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38527 q selected
  have h2 (q : Pattern) (selected : d46523 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46524 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46525 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46526 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46532 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38529 q selected
    | true =>
      simp only [d46532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38530 q selected
  have h7 (q : Pattern) (selected : d46533 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46534 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46535 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46536 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46537 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38532 (p : Pattern) (selected : d46542 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46508 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38524 q selected
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46509 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46512 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38525 q selected
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46513 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46514 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46515 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46541 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46542 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38533 (p : Pattern) (selected : d46544 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46512 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38525 q selected
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46513 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46518 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46519 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46543 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46544 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38534 (p : Pattern) (selected : d46551 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46508 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38524 q selected
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46509 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46512 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38525 q selected
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46513 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46514 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46549 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46550 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46551 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38535 (p : Pattern) (selected : d46554 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46512 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38525 q selected
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46513 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46518 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46552 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46553 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46554 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38536 (p : Pattern) (selected : d46558 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46467 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38517 q selected
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46468 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46469 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46470 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46471 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46558 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38537 (p : Pattern) (selected : d46564 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46559 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38536 q selected
    | true =>
      simp only [d46559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38520 q selected
  have h2 (q : Pattern) (selected : d46560 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46561 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46491 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38520 q selected
    | true =>
      simp only [d46491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38521 q selected
  have h5 (q : Pattern) (selected : d46492 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46493 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46562 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46501 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38521 q selected
    | true =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38523 q selected
  have h9 (q : Pattern) (selected : d46502 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46503 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46504 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d46563 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46564 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro38538 (p : Pattern) (selected : d46570 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46565 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38537 q selected
    | true =>
      simp only [d46565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46566 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46508 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38524 q selected
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46509 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46567 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46568 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46569 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46570 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38539 (p : Pattern) (selected : d46573 p = 2) : d46460 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2 q = 2) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d158 q = 2) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d159 q = 2) : d14 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, d14, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d159, d14, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1233 q = 2) : d1084 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1233, d1084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1233, d1084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d45277 q = 2) : d44996 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d45277, d44996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45277, d44996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46572 q = 2) : d46459 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46572, d46459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46572, d46459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46573 q = 2) : d46460 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46573, d46460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46573, d46460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro38540 (p : Pattern) (selected : d46579 p = 2) : d46466 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46574 q = 2) : d46461 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46574, d46461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46574, d46461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38539 q selected
  have h2 (q : Pattern) (selected : d32325 q = 2) : d32155 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32325, d32155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32325, d32155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10574 q selected
  have h3 (q : Pattern) (selected : d46575 q = 2) : d46462 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46575, d46462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46575, d46462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46576 q = 2) : d46463 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46576, d46463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46576, d46463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46577 q = 2) : d46464 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46577, d46464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46577, d46464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46578 q = 2) : d46465 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46578, d46465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46578, d46465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46579 q = 2) : d46466 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46579, d46466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46579, d46466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro38541 (p : Pattern) (selected : d46586 p = 2) : d46473 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2 q = 2) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d158 q = 2) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d159 q = 2) : d14 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, d14, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d159, d14, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d160 q = 2) : d15 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d160, d15, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d160, d15, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46115 q = 2) : d45587 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d46115, d45587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46115, d45587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46585 q = 2) : d46472 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46585, d46472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46585, d46472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46586 q = 2) : d46473 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46586, d46473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46586, d46473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro38542 (p : Pattern) (selected : d46595 p = 2) : d46482 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46574 q = 2) : d46461 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46574, d46461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46574, d46461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38539 q selected
  have h2 (q : Pattern) (selected : d32325 q = 2) : d32155 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32325, d32155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32325, d32155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10574 q selected
  have h3 (q : Pattern) (selected : d46575 q = 2) : d46462 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46575, d46462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46575, d46462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46576 q = 2) : d46463 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46576, d46463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46576, d46463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46577 q = 2) : d46464 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46577, d46464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46577, d46464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46578 q = 2) : d46465 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46578, d46465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46578, d46465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46587 q = 2) : d46474 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46587, d46474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46587, d46474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38541 q selected
  have h8 (q : Pattern) (selected : d1270 q = 2) : d1115 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, d1115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1270, d1115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro667 q selected
  have h9 (q : Pattern) (selected : d46588 q = 2) : d46475 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46588, d46475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46588, d46475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46589 q = 2) : d46476 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46589, d46476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46589, d46476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46590 q = 2) : d46477 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46590, d46477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38541 q selected
    | true =>
      simp only [d46590, d46477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164 q = 2) : d19 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, d19, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro667 q selected
    | true =>
      simp only [d164, d19, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d46591 q = 2) : d46478 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46591, d46478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46591, d46478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46592 q = 2) : d46479 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46592, d46479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46592, d46479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46593 q = 2) : d46480 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46593, d46480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46593, d46480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d46594 q = 2) : d46481 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46594, d46481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d46594, d46481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d46595 q = 2) : d46482 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46595, d46482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46595, d46482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro38543 (p : Pattern) (selected : d46601 p = 2) : d46488 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46580 q = 2) : d46467 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46580, d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38540 q selected
    | true =>
      simp only [d46580, d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46581 q = 2) : d46468 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46581, d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46581, d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46582 q = 2) : d46469 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46582, d46469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46582, d46469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46583 q = 2) : d46470 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46583, d46470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46583, d46470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46584 q = 2) : d46471 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46584, d46471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46584, d46471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46596 q = 2) : d46483 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46596, d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38542 q selected
    | true =>
      simp only [d46596, d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46597 q = 2) : d46484 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46597, d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46597, d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46598 q = 2) : d46485 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46598, d46485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46598, d46485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46599 q = 2) : d46486 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46599, d46486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46599, d46486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46600 q = 2) : d46487 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46600, d46487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46600, d46487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46601 q = 2) : d46488 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46601, d46488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46601, d46488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38544 (p : Pattern) (selected : d46603 p = 2) : d46490 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46580 q = 2) : d46467 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46580, d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38540 q selected
    | true =>
      simp only [d46580, d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46581 q = 2) : d46468 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46581, d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46581, d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46582 q = 2) : d46469 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46582, d46469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46582, d46469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46583 q = 2) : d46470 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46583, d46470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46583, d46470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46596 q = 2) : d46483 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46596, d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38542 q selected
    | true =>
      simp only [d46596, d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46597 q = 2) : d46484 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46597, d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46597, d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46598 q = 2) : d46485 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46598, d46485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46598, d46485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46599 q = 2) : d46486 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46599, d46486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46599, d46486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46600 q = 2) : d46487 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46600, d46487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46600, d46487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46602 q = 2) : d46489 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46602, d46489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46602, d46489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46603 q = 2) : d46490 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46603, d46490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46603, d46490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38545 (p : Pattern) (selected : d46607 p = 2) : d46494 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46587 q = 2) : d46474 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46587, d46474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46587, d46474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38541 q selected
  have h2 (q : Pattern) (selected : d1270 q = 2) : d1115 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, d1115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1270, d1115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro667 q selected
  have h3 (q : Pattern) (selected : d46588 q = 2) : d46475 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46588, d46475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46588, d46475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46589 q = 2) : d46476 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46589, d46476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46589, d46476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46590 q = 2) : d46477 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46590, d46477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38541 q selected
    | true =>
      simp only [d46590, d46477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164 q = 2) : d19 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, d19, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro667 q selected
    | true =>
      simp only [d164, d19, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46591 q = 2) : d46478 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46591, d46478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46591, d46478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46592 q = 2) : d46479 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46592, d46479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46592, d46479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46593 q = 2) : d46480 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46593, d46480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46593, d46480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46594 q = 2) : d46481 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46594, d46481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46594, d46481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46607 q = 2) : d46494 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46607, d46494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46607, d46494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h11 p selected
theorem eqIntro38546 (p : Pattern) (selected : d46613 p = 2) : d46500 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46596 q = 2) : d46483 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46596, d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38542 q selected
    | true =>
      simp only [d46596, d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46597 q = 2) : d46484 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46597, d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46597, d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46598 q = 2) : d46485 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46598, d46485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46598, d46485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46599 q = 2) : d46486 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46599, d46486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46599, d46486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46602 q = 2) : d46489 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46602, d46489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46602, d46489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46608 q = 2) : d46495 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46608, d46495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38545 q selected
    | true =>
      simp only [d46608, d46495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46609 q = 2) : d46496 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46609, d46496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46609, d46496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46610 q = 2) : d46497 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46610, d46497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46610, d46497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46611 q = 2) : d46498 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46611, d46498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46611, d46498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46612 q = 2) : d46499 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46612, d46499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46612, d46499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46613 q = 2) : d46500 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46613, d46500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46613, d46500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38547 (p : Pattern) (selected : d46620 p = 2) : d46507 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46604 q = 2) : d46491 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46604, d46491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38543 q selected
    | true =>
      simp only [d46604, d46491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38544 q selected
  have h2 (q : Pattern) (selected : d46605 q = 2) : d46492 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46605, d46492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46605, d46492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46606 q = 2) : d46493 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46606, d46493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46606, d46493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46614 q = 2) : d46501 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46614, d46501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38544 q selected
    | true =>
      simp only [d46614, d46501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38546 q selected
  have h5 (q : Pattern) (selected : d46615 q = 2) : d46502 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46615, d46502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46615, d46502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46616 q = 2) : d46503 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46616, d46503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46616, d46503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46617 q = 2) : d46504 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46617, d46504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46617, d46504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46618 q = 2) : d46505 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46618, d46505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46618, d46505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46619 q = 2) : d46506 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46619, d46506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46619, d46506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46620 q = 2) : d46507 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46620, d46507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46620, d46507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38548 (p : Pattern) (selected : d46624 p = 2) : d46511 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46614 q = 2) : d46501 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46614, d46501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38544 q selected
    | true =>
      simp only [d46614, d46501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38546 q selected
  have h2 (q : Pattern) (selected : d46615 q = 2) : d46502 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46615, d46502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46615, d46502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46616 q = 2) : d46503 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46616, d46503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46616, d46503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46618 q = 2) : d46505 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46618, d46505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46618, d46505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46623 q = 2) : d46510 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46623, d46510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46623, d46510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46624 q = 2) : d46511 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46624, d46511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46624, d46511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38549 (p : Pattern) (selected : d46630 p = 2) : d46517 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46621 q = 2) : d46508 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46621, d46508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38547 q selected
    | true =>
      simp only [d46621, d46508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46622 q = 2) : d46509 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46622, d46509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46622, d46509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46625 q = 2) : d46512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46625, d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38548 q selected
    | true =>
      simp only [d46625, d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46626 q = 2) : d46513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46626, d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46626, d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46627 q = 2) : d46514 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46627, d46514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46627, d46514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46628 q = 2) : d46515 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46628, d46515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46628, d46515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46629 q = 2) : d46516 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46629, d46516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46629, d46516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46630 q = 2) : d46517 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46630, d46517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46630, d46517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38550 (p : Pattern) (selected : d46634 p = 2) : d46521 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46625 q = 2) : d46512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46625, d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38548 q selected
    | true =>
      simp only [d46625, d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46626 q = 2) : d46513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46626, d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46626, d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46631 q = 2) : d46518 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46631, d46518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46631, d46518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46632 q = 2) : d46519 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46632, d46519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46632, d46519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46633 q = 2) : d46520 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46633, d46520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46633, d46520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46634 q = 2) : d46521 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46634, d46521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46634, d46521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38551 (p : Pattern) (selected : d46637 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46461 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38516 q selected
  have h2 (q : Pattern) (selected : d32155 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10556 q selected
  have h3 (q : Pattern) (selected : d46462 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46463 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46464 q = 2) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46465 q = 2) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46637 q = 2) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro38552 (p : Pattern) (selected : d46643 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46467 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38517 q selected
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46468 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46469 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46470 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46483 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38519 q selected
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46484 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46485 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46486 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46487 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46638 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38551 q selected
    | true =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46639 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d46640 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46641 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d46642 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46643 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38553 (p : Pattern) (selected : d46644 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46638 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38551 q selected
    | true =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46639 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46640 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46641 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46642 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46644 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38554 (p : Pattern) (selected : d46650 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46491 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38520 q selected
    | true =>
      simp only [d46491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38521 q selected
  have h2 (q : Pattern) (selected : d46492 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46493 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46501 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38521 q selected
    | true =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38523 q selected
  have h5 (q : Pattern) (selected : d46502 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46503 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46504 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46645 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38552 q selected
    | true =>
      simp only [d46645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38553 q selected
  have h9 (q : Pattern) (selected : d46646 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46647 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46648 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d46649 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46650 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro38555 (p : Pattern) (selected : d46656 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46651 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38554 q selected
    | true =>
      simp only [d46651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46652 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46653 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46654 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46655 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46656 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38556 (p : Pattern) (selected : d46662 p = 2) : d46527 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46545 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38532 q selected
    | true =>
      simp only [d46545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38533 q selected
  have h2 (q : Pattern) (selected : d46546 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46547 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46548 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46555 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38534 q selected
    | true =>
      simp only [d46555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38535 q selected
  have h6 (q : Pattern) (selected : d46556 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46557 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46571 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38538 q selected
    | true =>
      simp only [d46571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38526 q selected
  have h9 (q : Pattern) (selected : d46635 q = 2) : d46522 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46635, d46522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38549 q selected
    | true =>
      simp only [d46635, d46522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38550 q selected
  have h10 (q : Pattern) (selected : d46636 q = 2) : d46523 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46636, d46523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46636, d46523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46657 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38555 q selected
    | true =>
      simp only [d46657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d46658 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d46659 q = 2) : d46524 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46659, d46524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46659, d46524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46660 q = 2) : d46525 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46660, d46525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46660, d46525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d46661 q = 2) : d46526 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46661, d46526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46661, d46526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d46662 q = 2) : d46527 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46662, d46527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46662, d46527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro38557 (p : Pattern) (selected : d46663 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46508 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38524 q selected
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46509 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46512 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38525 q selected
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46513 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46514 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46515 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46541 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46663 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38558 (p : Pattern) (selected : d46664 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46512 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38525 q selected
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46513 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46518 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46519 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46543 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46664 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38559 (p : Pattern) (selected : d46669 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46508 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38524 q selected
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46509 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46512 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38525 q selected
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46513 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46514 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46549 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46550 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46669 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38560 (p : Pattern) (selected : d46670 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46512 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38525 q selected
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46513 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46518 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46552 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46553 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46670 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38561 (p : Pattern) (selected : d46674 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46565 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38537 q selected
    | true =>
      simp only [d46565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46566 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46508 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38524 q selected
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46509 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46567 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46568 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46569 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46674 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38562 (p : Pattern) (selected : d46676 p = 2) : d46530 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46621 q = 2) : d46508 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46621, d46508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38547 q selected
    | true =>
      simp only [d46621, d46508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46622 q = 2) : d46509 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46622, d46509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46622, d46509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46625 q = 2) : d46512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46625, d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38548 q selected
    | true =>
      simp only [d46625, d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46626 q = 2) : d46513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46626, d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46626, d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46627 q = 2) : d46514 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46627, d46514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46627, d46514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46628 q = 2) : d46515 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46628, d46515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46628, d46515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46629 q = 2) : d46516 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46629, d46516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46629, d46516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46676 q = 2) : d46530 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46676, d46530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46676, d46530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38563 (p : Pattern) (selected : d46677 p = 2) : d46531 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46625 q = 2) : d46512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46625, d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38548 q selected
    | true =>
      simp only [d46625, d46512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46626 q = 2) : d46513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46626, d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46626, d46513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46631 q = 2) : d46518 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46631, d46518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46631, d46518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46632 q = 2) : d46519 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46632, d46519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46632, d46519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46633 q = 2) : d46520 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46633, d46520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46633, d46520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46677 q = 2) : d46531 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46677, d46531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46677, d46531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38564 (p : Pattern) (selected : d46680 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46651 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38554 q selected
    | true =>
      simp only [d46651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46652 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46653 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46654 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46655 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46680 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38565 (p : Pattern) (selected : d46686 p = 2) : d46537 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46545 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38532 q selected
    | true =>
      simp only [d46545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38533 q selected
  have h2 (q : Pattern) (selected : d46546 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46547 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46548 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46555 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38534 q selected
    | true =>
      simp only [d46555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38535 q selected
  have h6 (q : Pattern) (selected : d46556 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46557 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46571 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38538 q selected
    | true =>
      simp only [d46571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38526 q selected
  have h9 (q : Pattern) (selected : d46635 q = 2) : d46522 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46635, d46522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38549 q selected
    | true =>
      simp only [d46635, d46522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38550 q selected
  have h10 (q : Pattern) (selected : d46636 q = 2) : d46523 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46636, d46523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46636, d46523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46657 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38555 q selected
    | true =>
      simp only [d46657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d46658 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d46659 q = 2) : d46524 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46659, d46524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46659, d46524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46660 q = 2) : d46525 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46660, d46525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46660, d46525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d46661 q = 2) : d46526 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46661, d46526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46661, d46526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d46665 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38557 q selected
    | true =>
      simp only [d46665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38558 q selected
  have h17 (q : Pattern) (selected : d46666 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d46667 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d46667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d46668 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d46671 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38559 q selected
    | true =>
      simp only [d46671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38560 q selected
  have h21 (q : Pattern) (selected : d46672 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d46673 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d46673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d46675 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38561 q selected
    | true =>
      simp only [d46675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38529 q selected
  have h24 (q : Pattern) (selected : d46678 q = 2) : d46532 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46678, d46532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38562 q selected
    | true =>
      simp only [d46678, d46532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38563 q selected
  have h25 (q : Pattern) (selected : d46679 q = 2) : d46533 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46679, d46533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d46679, d46533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d46681 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38564 q selected
    | true =>
      simp only [d46681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d46682 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d46682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d46683 q = 2) : d46534 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46683, d46534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d46683, d46534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d46684 q = 2) : d46535 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46684, d46535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d46684, d46535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d46685 q = 2) : d46536 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46685, d46536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d46685, d46536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d46686 q = 2) : d46537 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46686, d46537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d46686, d46537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro38566 (p : Pattern) (selected : d46693 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46522 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38526 q selected
    | true =>
      simp only [d46522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38527 q selected
  have h2 (q : Pattern) (selected : d46523 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46524 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46525 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46526 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46688 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38527 q selected
    | true =>
      simp only [d46688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46689 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46690 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46691 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46692 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46693 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38567 (p : Pattern) (selected : d46699 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46688 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38527 q selected
    | true =>
      simp only [d46688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46689 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46690 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46691 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46692 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46694 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38530 q selected
    | true =>
      simp only [d46694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46695 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46696 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46697 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46698 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46699 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38568 (p : Pattern) (selected : d46706 p = 2) : d321880 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46675 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38561 q selected
    | true =>
      simp only [d46675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38529 q selected
  have h2 (q : Pattern) (selected : d46678 q = 2) : d46532 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46678, d46532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38562 q selected
    | true =>
      simp only [d46678, d46532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38563 q selected
  have h3 (q : Pattern) (selected : d46679 q = 2) : d46533 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46679, d46533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46679, d46533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46681 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38564 q selected
    | true =>
      simp only [d46681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46682 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46683 q = 2) : d46534 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46683, d46534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46683, d46534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46704 q = 2) : d46535 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46704, d46535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46704, d46535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46705 q = 2) : d46536 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46705, d46536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46705, d46536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46706 q = 2) : d321880 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46706, d321880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46706, d321880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38569 (p : Pattern) (selected : d46708 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46694 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38530 q selected
    | true =>
      simp only [d46694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46695 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46696 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46697 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46698 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46708 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38570 (p : Pattern) (selected : d46719 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46714 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38517 q selected
  have h2 (q : Pattern) (selected : d46467 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38517 q selected
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46715 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46468 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46716 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46717 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46718 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46719 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38571 (p : Pattern) (selected : d46725 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46714 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38517 q selected
  have h2 (q : Pattern) (selected : d46467 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38517 q selected
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46715 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46468 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46716 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46717 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46718 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46720 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38519 q selected
  have h9 (q : Pattern) (selected : d46483 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38519 q selected
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46721 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46484 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d46722 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46723 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d46724 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d46725 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38572 (p : Pattern) (selected : d46730 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46714 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38517 q selected
  have h2 (q : Pattern) (selected : d46467 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38517 q selected
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46715 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46468 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46716 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46717 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46720 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38519 q selected
  have h8 (q : Pattern) (selected : d46483 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38519 q selected
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46721 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46484 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46722 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d46723 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d46724 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46729 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46730 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38573 (p : Pattern) (selected : d46740 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46720 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38519 q selected
  have h2 (q : Pattern) (selected : d46483 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38519 q selected
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46721 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46484 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46722 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46723 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46729 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46735 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38522 q selected
  have h9 (q : Pattern) (selected : d46495 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38522 q selected
    | true =>
      simp only [d46495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46736 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46496 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d46737 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46738 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d46739 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46740 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38574 (p : Pattern) (selected : d46746 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46726 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38570 q selected
    | true =>
      simp only [d46726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38571 q selected
  have h2 (q : Pattern) (selected : d46727 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46728 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46731 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38571 q selected
    | true =>
      simp only [d46731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38572 q selected
  have h5 (q : Pattern) (selected : d46732 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46733 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46734 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46741 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38572 q selected
    | true =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38573 q selected
  have h9 (q : Pattern) (selected : d46742 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46743 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46744 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d46745 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46746 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro38575 (p : Pattern) (selected : d46751 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46731 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38571 q selected
    | true =>
      simp only [d46731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38572 q selected
  have h2 (q : Pattern) (selected : d46732 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46733 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46741 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38572 q selected
    | true =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38573 q selected
  have h5 (q : Pattern) (selected : d46742 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46743 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46744 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46749 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46750 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46751 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38576 (p : Pattern) (selected : d46757 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46747 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38574 q selected
    | true =>
      simp only [d46747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46748 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46752 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38575 q selected
    | true =>
      simp only [d46752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46753 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46754 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46755 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46756 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46757 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38577 (p : Pattern) (selected : d46759 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46741 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38572 q selected
    | true =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38573 q selected
  have h2 (q : Pattern) (selected : d46742 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46743 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46749 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46758 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46759 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38578 (p : Pattern) (selected : d46765 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46752 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38575 q selected
    | true =>
      simp only [d46752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46753 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46760 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38577 q selected
    | true =>
      simp only [d46760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46761 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46762 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46763 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46764 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46765 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38579 (p : Pattern) (selected : d46777 p = 2) : d46725 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46767 q = 2) : d46714 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46767, d46714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46767, d46714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38540 q selected
  have h2 (q : Pattern) (selected : d46580 q = 2) : d46467 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46580, d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38540 q selected
    | true =>
      simp only [d46580, d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46768 q = 2) : d46715 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46768, d46715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46768, d46715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46581 q = 2) : d46468 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46581, d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46581, d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46769 q = 2) : d46716 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46769, d46716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46769, d46716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46770 q = 2) : d46717 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46770, d46717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46770, d46717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46771 q = 2) : d46718 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46771, d46718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46771, d46718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46772 q = 2) : d46720 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46772, d46720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46772, d46720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38542 q selected
  have h9 (q : Pattern) (selected : d46596 q = 2) : d46483 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46596, d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38542 q selected
    | true =>
      simp only [d46596, d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46773 q = 2) : d46721 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46773, d46721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46773, d46721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46597 q = 2) : d46484 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46597, d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46597, d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d46774 q = 2) : d46722 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46774, d46722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46774, d46722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46775 q = 2) : d46723 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46775, d46723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46775, d46723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d46776 q = 2) : d46724 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46776, d46724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46776, d46724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d46777 q = 2) : d46725 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46777, d46725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46777, d46725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38580 (p : Pattern) (selected : d46779 p = 2) : d46730 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46767 q = 2) : d46714 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46767, d46714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46767, d46714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38540 q selected
  have h2 (q : Pattern) (selected : d46580 q = 2) : d46467 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46580, d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38540 q selected
    | true =>
      simp only [d46580, d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46768 q = 2) : d46715 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46768, d46715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46768, d46715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46581 q = 2) : d46468 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46581, d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46581, d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46769 q = 2) : d46716 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46769, d46716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46769, d46716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46770 q = 2) : d46717 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46770, d46717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46770, d46717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46772 q = 2) : d46720 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46772, d46720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46772, d46720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38542 q selected
  have h8 (q : Pattern) (selected : d46596 q = 2) : d46483 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46596, d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38542 q selected
    | true =>
      simp only [d46596, d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46773 q = 2) : d46721 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46773, d46721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46773, d46721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46597 q = 2) : d46484 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46597, d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46597, d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46774 q = 2) : d46722 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46774, d46722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46774, d46722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d46775 q = 2) : d46723 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46775, d46723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46775, d46723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d46776 q = 2) : d46724 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46776, d46724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46776, d46724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46778 q = 2) : d46729 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46778, d46729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46778, d46729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46779 q = 2) : d46730 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46779, d46730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46779, d46730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38581 (p : Pattern) (selected : d46788 p = 2) : d46740 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46772 q = 2) : d46720 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46772, d46720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46772, d46720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38542 q selected
  have h2 (q : Pattern) (selected : d46596 q = 2) : d46483 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46596, d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38542 q selected
    | true =>
      simp only [d46596, d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46773 q = 2) : d46721 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46773, d46721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46773, d46721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46597 q = 2) : d46484 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46597, d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46597, d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46774 q = 2) : d46722 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46774, d46722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46774, d46722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46775 q = 2) : d46723 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46775, d46723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46775, d46723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46778 q = 2) : d46729 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46778, d46729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46778, d46729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46783 q = 2) : d46735 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46783, d46735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46783, d46735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38545 q selected
  have h9 (q : Pattern) (selected : d46608 q = 2) : d46495 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46608, d46495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38545 q selected
    | true =>
      simp only [d46608, d46495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46784 q = 2) : d46736 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46784, d46736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46784, d46736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46609 q = 2) : d46496 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46609, d46496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46609, d46496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d46785 q = 2) : d46737 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46785, d46737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46785, d46737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46786 q = 2) : d46738 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46786, d46738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46786, d46738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d46787 q = 2) : d46739 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46787, d46739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46787, d46739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46788 q = 2) : d46740 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46788, d46740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46788, d46740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38582 (p : Pattern) (selected : d46795 p = 2) : d46751 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46780 q = 2) : d46731 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46780, d46731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38579 q selected
    | true =>
      simp only [d46780, d46731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38580 q selected
  have h2 (q : Pattern) (selected : d46781 q = 2) : d46732 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46781, d46732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46781, d46732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46782 q = 2) : d46733 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46782, d46733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46782, d46733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46789 q = 2) : d46741 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46789, d46741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38580 q selected
    | true =>
      simp only [d46789, d46741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38581 q selected
  have h5 (q : Pattern) (selected : d46790 q = 2) : d46742 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46790, d46742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46790, d46742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46791 q = 2) : d46743 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46791, d46743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46791, d46743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46792 q = 2) : d46744 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46792, d46744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46792, d46744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46793 q = 2) : d46749 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46793, d46749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46793, d46749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46794 q = 2) : d46750 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46794, d46750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46794, d46750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46795 q = 2) : d46751 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46795, d46751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46795, d46751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38583 (p : Pattern) (selected : d46799 p = 2) : d46759 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46789 q = 2) : d46741 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46789, d46741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38580 q selected
    | true =>
      simp only [d46789, d46741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38581 q selected
  have h2 (q : Pattern) (selected : d46790 q = 2) : d46742 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46790, d46742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46790, d46742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46791 q = 2) : d46743 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46791, d46743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46791, d46743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46793 q = 2) : d46749 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46793, d46749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46793, d46749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46798 q = 2) : d46758 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46798, d46758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46798, d46758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46799 q = 2) : d46759 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46799, d46759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46799, d46759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38584 (p : Pattern) (selected : d46805 p = 2) : d46765 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46796 q = 2) : d46752 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46796, d46752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38582 q selected
    | true =>
      simp only [d46796, d46752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46797 q = 2) : d46753 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46797, d46753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46797, d46753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46800 q = 2) : d46760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46800, d46760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38583 q selected
    | true =>
      simp only [d46800, d46760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46801 q = 2) : d46761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46801, d46761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46801, d46761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46802 q = 2) : d46762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46802, d46762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46802, d46762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46803 q = 2) : d46763 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46803, d46763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46803, d46763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46804 q = 2) : d46764 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46804, d46764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46804, d46764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46805 q = 2) : d46765 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46805, d46765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46805, d46765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38585 (p : Pattern) (selected : d46809 p = 2) : d46841 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46800 q = 2) : d46760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46800, d46760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38583 q selected
    | true =>
      simp only [d46800, d46760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46801 q = 2) : d46761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46801, d46761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46801, d46761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46806 q = 2) : d46838 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46806, d46838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46806, d46838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46807 q = 2) : d46839 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46807, d46839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46807, d46839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46808 q = 2) : d46840 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46808, d46840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46808, d46840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46809 q = 2) : d46841 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46809, d46841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46809, d46841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38586 (p : Pattern) (selected : d46817 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46714 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38517 q selected
  have h2 (q : Pattern) (selected : d46467 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38517 q selected
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46715 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46468 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46716 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46717 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46720 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38519 q selected
  have h8 (q : Pattern) (selected : d46483 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38519 q selected
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46721 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46484 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46722 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d46723 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d46724 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46812 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38551 q selected
  have h15 (q : Pattern) (selected : d46638 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38551 q selected
    | true =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d46813 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d46813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d46639 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d46814 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d46814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d46815 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d46815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d46816 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d46816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d46817 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro38587 (p : Pattern) (selected : d46818 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46812 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38551 q selected
  have h2 (q : Pattern) (selected : d46638 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38551 q selected
    | true =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46813 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46639 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46814 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46815 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46816 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46818 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38588 (p : Pattern) (selected : d46824 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46731 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38571 q selected
    | true =>
      simp only [d46731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38572 q selected
  have h2 (q : Pattern) (selected : d46732 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46733 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46741 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38572 q selected
    | true =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38573 q selected
  have h5 (q : Pattern) (selected : d46742 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46743 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46744 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46819 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38586 q selected
    | true =>
      simp only [d46819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38587 q selected
  have h9 (q : Pattern) (selected : d46820 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46821 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46822 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d46823 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46824 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro38589 (p : Pattern) (selected : d46830 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46825 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38588 q selected
    | true =>
      simp only [d46825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46826 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46827 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46828 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46829 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46830 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38590 (p : Pattern) (selected : d46836 p = 2) : d321891 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46766 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38576 q selected
    | true =>
      simp only [d46766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38578 q selected
  have h2 (q : Pattern) (selected : d46810 q = 2) : d321886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46810, d321886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38584 q selected
    | true =>
      simp only [d46810, d321886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38585 q selected
  have h3 (q : Pattern) (selected : d46811 q = 2) : d321887 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46811, d321887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46811, d321887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46831 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38589 q selected
    | true =>
      simp only [d46831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46832 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46833 q = 2) : d321888 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46833, d321888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46833, d321888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46834 q = 2) : d321889 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46834, d321889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46834, d321889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46835 q = 2) : d321890 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46835, d321890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46835, d321890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46836 q = 2) : d321891 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46836, d321891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46836, d321891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38591 (p : Pattern) (selected : d46841 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46760 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38577 q selected
    | true =>
      simp only [d46760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46761 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46838 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46839 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46840 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46841 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38592 (p : Pattern) (selected : d46847 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46842 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38591 q selected
    | true =>
      simp only [d46842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46843 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46844 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46845 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46846 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46847 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38593 (p : Pattern) (selected : d46853 p = 2) : d321897 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46528 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38528 q selected
  have h2 (q : Pattern) (selected : d46529 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46538 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38528 q selected
    | true =>
      simp only [d46538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38531 q selected
  have h4 (q : Pattern) (selected : d46539 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46540 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46687 q = 2) : d46538 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46687, d46538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38556 q selected
    | true =>
      simp only [d46687, d46538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38565 q selected
  have h7 (q : Pattern) (selected : d46700 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38566 q selected
    | true =>
      simp only [d46700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38567 q selected
  have h8 (q : Pattern) (selected : d46701 q = 2) : d46539 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46701, d46539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46701, d46539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46702 q = 2) : d321878 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46702, d321878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46702, d321878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46703 q = 2) : d321879 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d46703, d321879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46703, d321879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46707 q = 2) : d321881 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46707, d321881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46707, d321881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38568 q selected
  have h12 (q : Pattern) (selected : d46709 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38569 q selected
  have h13 (q : Pattern) (selected : d46710 q = 2) : d321882 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46710, d321882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46710, d321882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46711 q = 2) : d321883 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46711, d321883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46711, d321883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46712 q = 2) : d321884 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d46712, d321884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d46712, d321884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d46713 q = 2) : d321885 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d46713, d321885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46713, d321885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d46837 q = 2) : d321892 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46837, d321892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46837, d321892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38590 q selected
  have h18 (q : Pattern) (selected : d46848 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38592 q selected
  have h19 (q : Pattern) (selected : d46849 q = 2) : d321893 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46849, d321893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d46849, d321893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d46850 q = 2) : d321894 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46850, d321894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d46850, d321894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d46851 q = 2) : d321895 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d46851, d321895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d46851, d321895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d46852 q = 2) : d321896 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d46852, d321896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d46852, d321896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d46853 q = 2) : d321897 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d46853, d321897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d46853, d321897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro38594 (p : Pattern) (selected : d46859 p = 2) : d321903 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46854 q = 2) : d321898 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d46854, d321898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46854, d321898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38593 q selected
  have h2 (q : Pattern) (selected : d46855 q = 2) : d321899 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d46855, d321899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46855, d321899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46856 q = 2) : d321900 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d46856, d321900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46856, d321900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46857 q = 2) : d321901 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d46857, d321901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46857, d321901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46858 q = 2) : d321902 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d46858, d321902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46858, d321902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46859 q = 2) : d321903 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d46859, d321903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46859, d321903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38595 (p : Pattern) (selected : d46867 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1 q = 2) : d0 q = 1 := by
    change (1 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d13 q = 2) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44880 q = 2) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d44880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46864 q = 2) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d46864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46865 q = 2) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d46865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46866 q = 2) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46867 q = 2) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro38596 (p : Pattern) (selected : d46876 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46868 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38595 q selected
  have h2 (q : Pattern) (selected : d46869 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46870 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46871 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38595 q selected
    | true =>
      simp only [d46871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46872 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46873 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46874 q = 2) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46875 q = 2) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46876 q = 2) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38597 (p : Pattern) (selected : d46882 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46877 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38596 q selected
    | true =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46878 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46879 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46880 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46881 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46882 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38598 (p : Pattern) (selected : d46884 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46877 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38596 q selected
    | true =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46878 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46879 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46880 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46881 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46883 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46884 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro38599 (p : Pattern) (selected : d46888 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46868 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38595 q selected
  have h2 (q : Pattern) (selected : d46869 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46870 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46871 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38595 q selected
    | true =>
      simp only [d46871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46872 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46873 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46874 q = 2) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46875 q = 2) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46888 q = 2) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro38600 (p : Pattern) (selected : d46894 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46877 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38596 q selected
    | true =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46878 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46879 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46880 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46883 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46889 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38599 q selected
    | true =>
      simp only [d46889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46890 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46891 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46892 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46893 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46894 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38601 (p : Pattern) (selected : d46901 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46885 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38597 q selected
    | true =>
      simp only [d46885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38598 q selected
  have h2 (q : Pattern) (selected : d46886 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46887 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46895 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38598 q selected
    | true =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38600 q selected
  have h5 (q : Pattern) (selected : d46896 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46897 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46898 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46899 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46900 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46901 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38602 (p : Pattern) (selected : d46905 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46895 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38598 q selected
    | true =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38600 q selected
  have h2 (q : Pattern) (selected : d46896 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46897 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46899 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46904 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46905 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38603 (p : Pattern) (selected : d46911 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46902 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38601 q selected
    | true =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46903 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46906 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38602 q selected
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46907 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46908 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46909 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46910 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46911 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38604 (p : Pattern) (selected : d46915 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46906 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38602 q selected
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46907 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46912 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46913 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46914 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46915 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38605 (p : Pattern) (selected : d46921 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46916 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38603 q selected
    | true =>
      simp only [d46916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38604 q selected
  have h2 (q : Pattern) (selected : d46917 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46918 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46919 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46920 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46921 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38606 (p : Pattern) (selected : d46924 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46902 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38601 q selected
    | true =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46903 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46906 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38602 q selected
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46907 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46908 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46909 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46910 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46924 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38607 (p : Pattern) (selected : d46925 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46906 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38602 q selected
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46907 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46912 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46913 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46914 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46925 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38608 (p : Pattern) (selected : d46931 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46916 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38603 q selected
    | true =>
      simp only [d46916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38604 q selected
  have h2 (q : Pattern) (selected : d46917 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46918 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46919 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46920 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46926 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38606 q selected
    | true =>
      simp only [d46926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38607 q selected
  have h7 (q : Pattern) (selected : d46927 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46928 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46929 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46930 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46931 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38609 (p : Pattern) (selected : d46936 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46902 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38601 q selected
    | true =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46903 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46906 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38602 q selected
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46907 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46908 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46909 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46935 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46936 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38610 (p : Pattern) (selected : d46938 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46906 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38602 q selected
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46907 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46912 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46913 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46937 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46938 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38611 (p : Pattern) (selected : d46945 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46902 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38601 q selected
    | true =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46903 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46906 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38602 q selected
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46907 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46908 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46943 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46944 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46945 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38612 (p : Pattern) (selected : d46948 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46906 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38602 q selected
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46907 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46912 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46946 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46947 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46948 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38613 (p : Pattern) (selected : d46957 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46952 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38597 q selected
  have h2 (q : Pattern) (selected : d46953 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46954 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46885 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38597 q selected
    | true =>
      simp only [d46885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38598 q selected
  have h5 (q : Pattern) (selected : d46886 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46887 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46955 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46895 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38598 q selected
    | true =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38600 q selected
  have h9 (q : Pattern) (selected : d46896 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46897 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46898 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d46956 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46957 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro38614 (p : Pattern) (selected : d46963 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46958 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38613 q selected
    | true =>
      simp only [d46958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46959 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46902 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38601 q selected
    | true =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46903 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46960 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46961 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46962 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46963 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38615 (p : Pattern) (selected : d46965 p = 2) : d46867 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2 q = 2) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d158 q = 2) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d35873 q = 2) : d44880 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d35873, d44880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d35873, d44880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d35874 q = 2) : d46864 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d35874, d46864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d35874, d46864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d35875 q = 2) : d46865 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d35875, d46865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d35875, d46865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d35876 q = 2) : d46866 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d35876, d46866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d35876, d46866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46965 q = 2) : d46867 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46965, d46867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46965, d46867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro38616 (p : Pattern) (selected : d46974 p = 2) : d46876 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46966 q = 2) : d46868 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46966, d46868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46966, d46868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38615 q selected
  have h2 (q : Pattern) (selected : d46967 q = 2) : d46869 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46967, d46869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46967, d46869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46968 q = 2) : d46870 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46968, d46870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46968, d46870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46969 q = 2) : d46871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46969, d46871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38615 q selected
    | true =>
      simp only [d46969, d46871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46970 q = 2) : d46872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46970, d46872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46970, d46872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46971 q = 2) : d46873 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46971, d46873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46971, d46873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46972 q = 2) : d46874 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46972, d46874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46972, d46874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46973 q = 2) : d46875 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46973, d46875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46973, d46875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46974 q = 2) : d46876 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46974, d46876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46974, d46876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38617 (p : Pattern) (selected : d46980 p = 2) : d46882 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46975 q = 2) : d46877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46975, d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38616 q selected
    | true =>
      simp only [d46975, d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46976 q = 2) : d46878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46976, d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46976, d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46977 q = 2) : d46879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46977, d46879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46977, d46879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46978 q = 2) : d46880 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46978, d46880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46978, d46880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46979 q = 2) : d46881 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46979, d46881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46979, d46881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46980 q = 2) : d46882 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46980, d46882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46980, d46882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38618 (p : Pattern) (selected : d46982 p = 2) : d46884 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46975 q = 2) : d46877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46975, d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38616 q selected
    | true =>
      simp only [d46975, d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46976 q = 2) : d46878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46976, d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46976, d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46977 q = 2) : d46879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46977, d46879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46977, d46879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46978 q = 2) : d46880 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46978, d46880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46978, d46880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46979 q = 2) : d46881 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46979, d46881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46979, d46881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46981 q = 2) : d46883 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46981, d46883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46981, d46883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46982 q = 2) : d46884 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46982, d46884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46982, d46884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro38619 (p : Pattern) (selected : d46986 p = 2) : d46888 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46966 q = 2) : d46868 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46966, d46868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46966, d46868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38615 q selected
  have h2 (q : Pattern) (selected : d46967 q = 2) : d46869 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46967, d46869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46967, d46869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46968 q = 2) : d46870 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46968, d46870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46968, d46870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46969 q = 2) : d46871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46969, d46871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38615 q selected
    | true =>
      simp only [d46969, d46871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46970 q = 2) : d46872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46970, d46872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46970, d46872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46971 q = 2) : d46873 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46971, d46873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46971, d46873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46972 q = 2) : d46874 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46972, d46874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46972, d46874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46973 q = 2) : d46875 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46973, d46875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46973, d46875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46986 q = 2) : d46888 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46986, d46888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46986, d46888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro38620 (p : Pattern) (selected : d46992 p = 2) : d46894 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46975 q = 2) : d46877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46975, d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38616 q selected
    | true =>
      simp only [d46975, d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46976 q = 2) : d46878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46976, d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46976, d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46977 q = 2) : d46879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46977, d46879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46977, d46879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46978 q = 2) : d46880 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46978, d46880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46978, d46880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46981 q = 2) : d46883 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46981, d46883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46981, d46883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46987 q = 2) : d46889 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46987, d46889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38619 q selected
    | true =>
      simp only [d46987, d46889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46988 q = 2) : d46890 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46988, d46890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46988, d46890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46989 q = 2) : d46891 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46989, d46891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46989, d46891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46990 q = 2) : d46892 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46990, d46892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46990, d46892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46991 q = 2) : d46893 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46991, d46893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46991, d46893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46992 q = 2) : d46894 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46992, d46894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46992, d46894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38621 (p : Pattern) (selected : d46999 p = 2) : d46901 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46983 q = 2) : d46885 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46983, d46885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38617 q selected
    | true =>
      simp only [d46983, d46885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38618 q selected
  have h2 (q : Pattern) (selected : d46984 q = 2) : d46886 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46984, d46886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46984, d46886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46985 q = 2) : d46887 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46985, d46887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46985, d46887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46993 q = 2) : d46895 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46993, d46895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38618 q selected
    | true =>
      simp only [d46993, d46895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38620 q selected
  have h5 (q : Pattern) (selected : d46994 q = 2) : d46896 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46994, d46896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46994, d46896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46995 q = 2) : d46897 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46995, d46897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46995, d46897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46996 q = 2) : d46898 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46996, d46898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46996, d46898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46997 q = 2) : d46899 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46997, d46899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46997, d46899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46998 q = 2) : d46900 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46998, d46900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46998, d46900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46999 q = 2) : d46901 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46999, d46901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46999, d46901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38622 (p : Pattern) (selected : d47003 p = 2) : d46905 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46993 q = 2) : d46895 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46993, d46895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38618 q selected
    | true =>
      simp only [d46993, d46895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38620 q selected
  have h2 (q : Pattern) (selected : d46994 q = 2) : d46896 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46994, d46896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46994, d46896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46995 q = 2) : d46897 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46995, d46897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46995, d46897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46997 q = 2) : d46899 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46997, d46899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46997, d46899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47002 q = 2) : d46904 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47002, d46904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47002, d46904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47003 q = 2) : d46905 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47003, d46905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47003, d46905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38623 (p : Pattern) (selected : d47009 p = 2) : d46911 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47000 q = 2) : d46902 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47000, d46902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38621 q selected
    | true =>
      simp only [d47000, d46902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47001 q = 2) : d46903 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47001, d46903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47001, d46903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47004 q = 2) : d46906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47004, d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38622 q selected
    | true =>
      simp only [d47004, d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47005 q = 2) : d46907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47005, d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47005, d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47006 q = 2) : d46908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47006, d46908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47006, d46908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47007 q = 2) : d46909 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47007, d46909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47007, d46909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47008 q = 2) : d46910 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47008, d46910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47008, d46910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d47009 q = 2) : d46911 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47009, d46911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47009, d46911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38624 (p : Pattern) (selected : d47013 p = 2) : d46915 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47004 q = 2) : d46906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47004, d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38622 q selected
    | true =>
      simp only [d47004, d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47005 q = 2) : d46907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47005, d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47005, d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47010 q = 2) : d46912 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47010, d46912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47010, d46912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47011 q = 2) : d46913 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47011, d46913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47011, d46913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47012 q = 2) : d46914 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47012, d46914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47012, d46914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47013 q = 2) : d46915 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47013, d46915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47013, d46915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38625 (p : Pattern) (selected : d47016 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46877 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38596 q selected
    | true =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46878 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46879 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46880 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46881 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47016 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38626 (p : Pattern) (selected : d47022 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46885 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38597 q selected
    | true =>
      simp only [d46885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38598 q selected
  have h2 (q : Pattern) (selected : d46886 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46887 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46895 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38598 q selected
    | true =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38600 q selected
  have h5 (q : Pattern) (selected : d46896 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46897 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46898 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47017 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38625 q selected
    | true =>
      simp only [d47017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d47018 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d47019 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47020 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d47020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d47021 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d47022 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d47022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro38627 (p : Pattern) (selected : d47028 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47023 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38626 q selected
    | true =>
      simp only [d47023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47024 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47025 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47026 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47027 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47028 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38628 (p : Pattern) (selected : d47034 p = 2) : d46921 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46939 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38609 q selected
    | true =>
      simp only [d46939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38610 q selected
  have h2 (q : Pattern) (selected : d46940 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46941 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46942 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46949 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38611 q selected
    | true =>
      simp only [d46949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38612 q selected
  have h6 (q : Pattern) (selected : d46950 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46951 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46964 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38614 q selected
    | true =>
      simp only [d46964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38603 q selected
  have h9 (q : Pattern) (selected : d47014 q = 2) : d46916 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47014, d46916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38623 q selected
    | true =>
      simp only [d47014, d46916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38624 q selected
  have h10 (q : Pattern) (selected : d47015 q = 2) : d46917 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47015, d46917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d47015, d46917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47029 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38627 q selected
    | true =>
      simp only [d47029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d47030 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d47030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d47031 q = 2) : d46918 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47031, d46918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d47031, d46918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d47032 q = 2) : d46919 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47032, d46919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47032, d46919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d47033 q = 2) : d46920 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47033, d46920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47033, d46920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d47034 q = 2) : d46921 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47034, d46921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47034, d46921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro38629 (p : Pattern) (selected : d47035 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46902 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38601 q selected
    | true =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46903 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46906 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38602 q selected
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46907 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46908 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46909 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46935 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47035 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38630 (p : Pattern) (selected : d47036 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46906 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38602 q selected
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46907 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46912 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46913 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46937 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47036 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38631 (p : Pattern) (selected : d47041 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46902 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38601 q selected
    | true =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46903 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46906 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38602 q selected
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46907 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46908 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46943 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46944 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d47041 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38632 (p : Pattern) (selected : d47042 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46906 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38602 q selected
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46907 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46912 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46946 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46947 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47042 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38633 (p : Pattern) (selected : d47046 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46958 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38613 q selected
    | true =>
      simp only [d46958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46959 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46902 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38601 q selected
    | true =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46903 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46960 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46961 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46962 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d47046 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38634 (p : Pattern) (selected : d47048 p = 2) : d46924 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47000 q = 2) : d46902 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47000, d46902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38621 q selected
    | true =>
      simp only [d47000, d46902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47001 q = 2) : d46903 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47001, d46903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47001, d46903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47004 q = 2) : d46906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47004, d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38622 q selected
    | true =>
      simp only [d47004, d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47005 q = 2) : d46907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47005, d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47005, d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47006 q = 2) : d46908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47006, d46908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47006, d46908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47007 q = 2) : d46909 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47007, d46909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47007, d46909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47008 q = 2) : d46910 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47008, d46910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47008, d46910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d47048 q = 2) : d46924 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47048, d46924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47048, d46924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38635 (p : Pattern) (selected : d47049 p = 2) : d46925 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47004 q = 2) : d46906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47004, d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38622 q selected
    | true =>
      simp only [d47004, d46906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47005 q = 2) : d46907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47005, d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47005, d46907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47010 q = 2) : d46912 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47010, d46912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47010, d46912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47011 q = 2) : d46913 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47011, d46913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47011, d46913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47012 q = 2) : d46914 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47012, d46914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47012, d46914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47049 q = 2) : d46925 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47049, d46925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47049, d46925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38636 (p : Pattern) (selected : d47052 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47023 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38626 q selected
    | true =>
      simp only [d47023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47024 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47025 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47026 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47027 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47052 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38637 (p : Pattern) (selected : d47058 p = 2) : d46931 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46939 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38609 q selected
    | true =>
      simp only [d46939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38610 q selected
  have h2 (q : Pattern) (selected : d46940 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46941 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46942 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46949 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38611 q selected
    | true =>
      simp only [d46949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38612 q selected
  have h6 (q : Pattern) (selected : d46950 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46951 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46964 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38614 q selected
    | true =>
      simp only [d46964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38603 q selected
  have h9 (q : Pattern) (selected : d47014 q = 2) : d46916 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47014, d46916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38623 q selected
    | true =>
      simp only [d47014, d46916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38624 q selected
  have h10 (q : Pattern) (selected : d47015 q = 2) : d46917 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47015, d46917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d47015, d46917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47029 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38627 q selected
    | true =>
      simp only [d47029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d47030 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d47030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d47031 q = 2) : d46918 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47031, d46918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d47031, d46918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d47032 q = 2) : d46919 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47032, d46919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47032, d46919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d47033 q = 2) : d46920 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47033, d46920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47033, d46920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d47037 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38629 q selected
    | true =>
      simp only [d47037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38630 q selected
  have h17 (q : Pattern) (selected : d47038 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d47039 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d47039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d47040 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d47043 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38631 q selected
    | true =>
      simp only [d47043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38632 q selected
  have h21 (q : Pattern) (selected : d47044 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d47045 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d47045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d47047 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38633 q selected
    | true =>
      simp only [d47047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38606 q selected
  have h24 (q : Pattern) (selected : d47050 q = 2) : d46926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47050, d46926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38634 q selected
    | true =>
      simp only [d47050, d46926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38635 q selected
  have h25 (q : Pattern) (selected : d47051 q = 2) : d46927 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47051, d46927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d47051, d46927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d47053 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38636 q selected
    | true =>
      simp only [d47053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d47054 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d47054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d47055 q = 2) : d46928 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47055, d46928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d47055, d46928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d47056 q = 2) : d46929 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47056, d46929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d47056, d46929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d47057 q = 2) : d46930 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47057, d46930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d47057, d46930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d47058 q = 2) : d46931 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47058, d46931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d47058, d46931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro38638 (p : Pattern) (selected : d47065 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46916 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38603 q selected
    | true =>
      simp only [d46916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38604 q selected
  have h2 (q : Pattern) (selected : d46917 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46918 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46919 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46920 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47060 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38604 q selected
    | true =>
      simp only [d47060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47061 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47062 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d47063 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d47064 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47065 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38639 (p : Pattern) (selected : d47071 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47060 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38604 q selected
    | true =>
      simp only [d47060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47061 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47062 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47063 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47064 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47066 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38607 q selected
    | true =>
      simp only [d47066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47067 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47068 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d47069 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d47070 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47071 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38640 (p : Pattern) (selected : d47078 p = 2) : d321910 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47047 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38633 q selected
    | true =>
      simp only [d47047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38606 q selected
  have h2 (q : Pattern) (selected : d47050 q = 2) : d46926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47050, d46926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38634 q selected
    | true =>
      simp only [d47050, d46926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38635 q selected
  have h3 (q : Pattern) (selected : d47051 q = 2) : d46927 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47051, d46927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47051, d46927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47053 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38636 q selected
    | true =>
      simp only [d47053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47054 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47055 q = 2) : d46928 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47055, d46928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47055, d46928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d47076 q = 2) : d46929 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47076, d46929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47076, d46929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47077 q = 2) : d46930 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47077, d46930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47077, d46930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d47078 q = 2) : d321910 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47078, d321910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47078, d321910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38641 (p : Pattern) (selected : d47080 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47066 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38607 q selected
    | true =>
      simp only [d47066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47067 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47068 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47069 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47070 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47080 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38642 (p : Pattern) (selected : d47091 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47086 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38596 q selected
  have h2 (q : Pattern) (selected : d46877 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38596 q selected
    | true =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47087 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46878 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47088 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47089 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47090 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47091 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38643 (p : Pattern) (selected : d47096 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47086 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38596 q selected
  have h2 (q : Pattern) (selected : d46877 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38596 q selected
    | true =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47087 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46878 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47088 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47089 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47090 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47095 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d47096 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38644 (p : Pattern) (selected : d47106 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47086 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38596 q selected
  have h2 (q : Pattern) (selected : d46877 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38596 q selected
    | true =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47087 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46878 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47088 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47089 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47095 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d47101 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38599 q selected
  have h9 (q : Pattern) (selected : d46889 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38599 q selected
    | true =>
      simp only [d46889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d47102 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d47102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46890 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d47103 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d47103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d47104 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d47104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d47105 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d47105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d47106 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38645 (p : Pattern) (selected : d47112 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47092 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38642 q selected
  have h2 (q : Pattern) (selected : d47093 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47094 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47097 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38642 q selected
    | true =>
      simp only [d47097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38643 q selected
  have h5 (q : Pattern) (selected : d47098 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47099 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d47100 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47107 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38643 q selected
    | true =>
      simp only [d47107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38644 q selected
  have h9 (q : Pattern) (selected : d47108 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d47109 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47110 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d47111 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d47112 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d47112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro38646 (p : Pattern) (selected : d47117 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47097 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38642 q selected
    | true =>
      simp only [d47097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38643 q selected
  have h2 (q : Pattern) (selected : d47098 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47099 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47107 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38643 q selected
    | true =>
      simp only [d47107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38644 q selected
  have h5 (q : Pattern) (selected : d47108 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47109 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d47110 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47115 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d47116 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d47117 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d47117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38647 (p : Pattern) (selected : d47123 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47113 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38645 q selected
    | true =>
      simp only [d47113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47114 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47118 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38646 q selected
    | true =>
      simp only [d47118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47119 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47120 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47121 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47122 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d47123 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38648 (p : Pattern) (selected : d47125 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47107 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38643 q selected
    | true =>
      simp only [d47107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38644 q selected
  have h2 (q : Pattern) (selected : d47108 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47109 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47115 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47124 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47125 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38649 (p : Pattern) (selected : d47131 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47118 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38646 q selected
    | true =>
      simp only [d47118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47119 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47126 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38648 q selected
    | true =>
      simp only [d47126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47127 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47128 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47129 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47130 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d47131 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38650 (p : Pattern) (selected : d47138 p = 2) : d47091 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47133 q = 2) : d47086 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47133, d47086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47133, d47086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38616 q selected
  have h2 (q : Pattern) (selected : d46975 q = 2) : d46877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46975, d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38616 q selected
    | true =>
      simp only [d46975, d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47134 q = 2) : d47087 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47134, d47087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47134, d47087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46976 q = 2) : d46878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46976, d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46976, d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47135 q = 2) : d47088 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47135, d47088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47135, d47088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47136 q = 2) : d47089 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47136, d47089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47136, d47089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47137 q = 2) : d47090 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47137, d47090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47137, d47090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47138 q = 2) : d47091 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47138, d47091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47138, d47091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38651 (p : Pattern) (selected : d47140 p = 2) : d47096 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47133 q = 2) : d47086 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47133, d47086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47133, d47086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38616 q selected
  have h2 (q : Pattern) (selected : d46975 q = 2) : d46877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46975, d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38616 q selected
    | true =>
      simp only [d46975, d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47134 q = 2) : d47087 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47134, d47087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47134, d47087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46976 q = 2) : d46878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46976, d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46976, d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47135 q = 2) : d47088 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47135, d47088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47135, d47088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47136 q = 2) : d47089 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47136, d47089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47136, d47089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47137 q = 2) : d47090 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47137, d47090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47137, d47090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47139 q = 2) : d47095 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47139, d47095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47139, d47095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d47140 q = 2) : d47096 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47140, d47096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47140, d47096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38652 (p : Pattern) (selected : d47149 p = 2) : d47106 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47133 q = 2) : d47086 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47133, d47086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47133, d47086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38616 q selected
  have h2 (q : Pattern) (selected : d46975 q = 2) : d46877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46975, d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38616 q selected
    | true =>
      simp only [d46975, d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47134 q = 2) : d47087 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47134, d47087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47134, d47087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46976 q = 2) : d46878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46976, d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46976, d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47135 q = 2) : d47088 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47135, d47088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47135, d47088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47136 q = 2) : d47089 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47136, d47089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47136, d47089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47139 q = 2) : d47095 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47139, d47095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47139, d47095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d47144 q = 2) : d47101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47144, d47101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47144, d47101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38619 q selected
  have h9 (q : Pattern) (selected : d46987 q = 2) : d46889 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46987, d46889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38619 q selected
    | true =>
      simp only [d46987, d46889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d47145 q = 2) : d47102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47145, d47102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d47145, d47102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46988 q = 2) : d46890 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46988, d46890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46988, d46890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d47146 q = 2) : d47103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47146, d47103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d47146, d47103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d47147 q = 2) : d47104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47147, d47104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d47147, d47104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d47148 q = 2) : d47105 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47148, d47105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d47148, d47105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d47149 q = 2) : d47106 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47149, d47106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47149, d47106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38653 (p : Pattern) (selected : d47156 p = 2) : d47117 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47141 q = 2) : d47097 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47141, d47097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38650 q selected
    | true =>
      simp only [d47141, d47097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38651 q selected
  have h2 (q : Pattern) (selected : d47142 q = 2) : d47098 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47142, d47098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47142, d47098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47143 q = 2) : d47099 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47143, d47099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47143, d47099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47150 q = 2) : d47107 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47150, d47107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38651 q selected
    | true =>
      simp only [d47150, d47107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38652 q selected
  have h5 (q : Pattern) (selected : d47151 q = 2) : d47108 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47151, d47108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47151, d47108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47152 q = 2) : d47109 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47152, d47109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47152, d47109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d47153 q = 2) : d47110 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47153, d47110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47153, d47110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47154 q = 2) : d47115 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47154, d47115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47154, d47115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d47155 q = 2) : d47116 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47155, d47116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47155, d47116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d47156 q = 2) : d47117 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47156, d47117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d47156, d47117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38654 (p : Pattern) (selected : d47160 p = 2) : d47125 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47150 q = 2) : d47107 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47150, d47107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38651 q selected
    | true =>
      simp only [d47150, d47107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38652 q selected
  have h2 (q : Pattern) (selected : d47151 q = 2) : d47108 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47151, d47108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47151, d47108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47152 q = 2) : d47109 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47152, d47109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47152, d47109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47154 q = 2) : d47115 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47154, d47115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47154, d47115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47159 q = 2) : d47124 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47159, d47124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47159, d47124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47160 q = 2) : d47125 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47160, d47125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47160, d47125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38655 (p : Pattern) (selected : d47166 p = 2) : d47131 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47157 q = 2) : d47118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47157, d47118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38653 q selected
    | true =>
      simp only [d47157, d47118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47158 q = 2) : d47119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47158, d47119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47158, d47119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47161 q = 2) : d47126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47161, d47126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38654 q selected
    | true =>
      simp only [d47161, d47126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47162 q = 2) : d47127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47162, d47127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47162, d47127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47163 q = 2) : d47128 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47163, d47128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47163, d47128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47164 q = 2) : d47129 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47164, d47129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47164, d47129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47165 q = 2) : d47130 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47165, d47130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47165, d47130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d47166 q = 2) : d47131 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47166, d47131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47166, d47131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38656 (p : Pattern) (selected : d47172 p = 2) : d326581 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47167 q = 2) : d326576 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d47167, d326576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34054 q selected
    | true =>
      simp only [d47167, d326576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38615 q selected
  have h2 (q : Pattern) (selected : d47168 q = 2) : d326577 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d47168, d326577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47168, d326577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47169 q = 2) : d326578 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d47169, d326578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47169, d326578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46969 q = 2) : d46871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46969, d46871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38615 q selected
    | true =>
      simp only [d46969, d46871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46970 q = 2) : d46872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46970, d46872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46970, d46872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46971 q = 2) : d46873 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46971, d46873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46971, d46873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47170 q = 2) : d326579 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d47170, d326579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47170, d326579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47171 q = 2) : d326580 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d47171, d326580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47171, d326580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d47172 q = 2) : d326581 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d47172, d326581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d47172, d326581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro38657 (p : Pattern) (selected : d47178 p = 2) : d326587 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47133 q = 2) : d47086 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47133, d47086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47133, d47086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38616 q selected
  have h2 (q : Pattern) (selected : d46975 q = 2) : d46877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46975, d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38616 q selected
    | true =>
      simp only [d46975, d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47134 q = 2) : d47087 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47134, d47087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47134, d47087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46976 q = 2) : d46878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46976, d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46976, d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47135 q = 2) : d47088 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47135, d47088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47135, d47088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47136 q = 2) : d47089 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47136, d47089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47136, d47089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47139 q = 2) : d47095 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47139, d47095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47139, d47095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d47144 q = 2) : d47101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47144, d47101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47144, d47101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38619 q selected
  have h9 (q : Pattern) (selected : d46987 q = 2) : d46889 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46987, d46889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38619 q selected
    | true =>
      simp only [d46987, d46889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d47145 q = 2) : d47102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47145, d47102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d47145, d47102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47173 q = 2) : d326582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47173, d326582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38656 q selected
    | true =>
      simp only [d47173, d326582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d47174 q = 2) : d326583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47174, d326583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d47174, d326583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d47175 q = 2) : d326584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47175, d326584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d47175, d326584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d47176 q = 2) : d326585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47176, d326585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d47176, d326585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d47177 q = 2) : d326586 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47177, d326586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d47177, d326586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d47178 q = 2) : d326587 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47178, d326587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47178, d326587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro38658 (p : Pattern) (selected : d47184 p = 2) : d326593 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47179 q = 2) : d326588 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47179, d326588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38651 q selected
    | true =>
      simp only [d47179, d326588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38657 q selected
  have h2 (q : Pattern) (selected : d47180 q = 2) : d326589 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47180, d326589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47180, d326589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47181 q = 2) : d326590 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47181, d326590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47181, d326590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47182 q = 2) : d326591 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47182, d326591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47182, d326591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47183 q = 2) : d326592 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47183, d326592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47183, d326592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47184 q = 2) : d326593 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47184, d326593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47184, d326593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38659 (p : Pattern) (selected : d47190 p = 2) : d326599 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47185 q = 2) : d326594 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47185, d326594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38658 q selected
    | true =>
      simp only [d47185, d326594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47186 q = 2) : d326595 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47186, d326595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47186, d326595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47187 q = 2) : d326596 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47187, d326596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47187, d326596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47188 q = 2) : d326597 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47188, d326597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47188, d326597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47189 q = 2) : d326598 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47189, d326598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47189, d326598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47190 q = 2) : d326599 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47190, d326599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47190, d326599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38660 (p : Pattern) (selected : d47193 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47086 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38596 q selected
  have h2 (q : Pattern) (selected : d46877 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38596 q selected
    | true =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47087 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46878 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47088 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47089 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47090 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47193 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38661 (p : Pattern) (selected : d47199 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47097 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38642 q selected
    | true =>
      simp only [d47097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38643 q selected
  have h2 (q : Pattern) (selected : d47098 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47099 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47107 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38643 q selected
    | true =>
      simp only [d47107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38644 q selected
  have h5 (q : Pattern) (selected : d47108 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47109 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d47110 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47194 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38660 q selected
    | true =>
      simp only [d47194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d47195 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d47196 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47197 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d47197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d47198 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d47199 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d47199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro38662 (p : Pattern) (selected : d47205 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47200 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38661 q selected
    | true =>
      simp only [d47200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47201 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47202 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47203 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47204 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47205 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38663 (p : Pattern) (selected : d47211 p = 2) : d326605 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47132 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38647 q selected
    | true =>
      simp only [d47132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38649 q selected
  have h2 (q : Pattern) (selected : d47191 q = 2) : d326600 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47191, d326600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38655 q selected
    | true =>
      simp only [d47191, d326600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38659 q selected
  have h3 (q : Pattern) (selected : d47192 q = 2) : d326601 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47192, d326601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47192, d326601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47206 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38662 q selected
    | true =>
      simp only [d47206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47207 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47208 q = 2) : d326602 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47208, d326602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47208, d326602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d47209 q = 2) : d326603 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47209, d326603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47209, d326603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47210 q = 2) : d326604 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47210, d326604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47210, d326604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d47211 q = 2) : d326605 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47211, d326605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47211, d326605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38664 (p : Pattern) (selected : d47216 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47126 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38648 q selected
    | true =>
      simp only [d47126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47127 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47213 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47214 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47215 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47216 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38665 (p : Pattern) (selected : d47222 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47217 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38664 q selected
    | true =>
      simp only [d47217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47218 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47219 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47220 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47221 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47222 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38666 (p : Pattern) (selected : d47228 p = 2) : d326611 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d46922 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38605 q selected
  have h2 (q : Pattern) (selected : d46923 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46932 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38605 q selected
    | true =>
      simp only [d46932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38608 q selected
  have h4 (q : Pattern) (selected : d46933 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46934 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47059 q = 2) : d46932 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d47059, d46932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38628 q selected
    | true =>
      simp only [d47059, d46932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38637 q selected
  have h7 (q : Pattern) (selected : d47072 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d47072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38638 q selected
    | true =>
      simp only [d47072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38639 q selected
  have h8 (q : Pattern) (selected : d47073 q = 2) : d46933 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d47073, d46933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47073, d46933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d47074 q = 2) : d321908 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d47074, d321908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d47074, d321908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d47075 q = 2) : d321909 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d47075, d321909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47075, d321909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47079 q = 2) : d321911 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d47079, d321911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47079, d321911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38640 q selected
  have h12 (q : Pattern) (selected : d47081 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d47081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38641 q selected
  have h13 (q : Pattern) (selected : d47082 q = 2) : d321912 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d47082, d321912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d47082, d321912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d47083 q = 2) : d321913 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d47083, d321913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d47083, d321913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d47084 q = 2) : d321914 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d47084, d321914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d47084, d321914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d47085 q = 2) : d321915 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d47085, d321915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d47085, d321915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d47212 q = 2) : d326606 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d47212, d326606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47212, d326606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38663 q selected
  have h18 (q : Pattern) (selected : d47223 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d47223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38665 q selected
  have h19 (q : Pattern) (selected : d47224 q = 2) : d326607 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d47224, d326607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d47224, d326607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d47225 q = 2) : d326608 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d47225, d326608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d47225, d326608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d47226 q = 2) : d326609 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d47226, d326609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d47226, d326609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d47227 q = 2) : d326610 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d47227, d326610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d47227, d326610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d47228 q = 2) : d326611 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d47228, d326611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d47228, d326611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro38667 (p : Pattern) (selected : d47234 p = 2) : d326617 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47229 q = 2) : d326612 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d47229, d326612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47229, d326612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38666 q selected
  have h2 (q : Pattern) (selected : d47230 q = 2) : d326613 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d47230, d326613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47230, d326613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47231 q = 2) : d326614 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d47231, d326614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47231, d326614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47232 q = 2) : d326615 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d47232, d326615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47232, d326615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47233 q = 2) : d326616 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d47233, d326616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47233, d326616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47234 q = 2) : d326617 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d47234, d326617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47234, d326617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38668 (p : Pattern) (selected : d47240 p = 2) : d367712 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 2) : d367652 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d367652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38288 q selected
    | true =>
      simp only [d45496, d367652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38350 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d45903 q = 2) : d367679 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45903, d367679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45903, d367679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38427 q selected
  have h3 (q : Pattern) (selected : d45904 q = 2) : d367680 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d45904, d367680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45904, d367680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46456 q = 2) : d367707 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d46456, d367707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46456, d367707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38515 q selected
  have h5 (q : Pattern) (selected : d46457 q = 2) : d367708 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d46457, d367708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46457, d367708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46458 q = 2) : d367709 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d46458, d367709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46458, d367709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46860 q = 2) : d321904 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d46860, d321904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46860, d321904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38594 q selected
  have h8 (q : Pattern) (selected : d46861 q = 2) : d321905 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d46861, d321905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46861, d321905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46862 q = 2) : d321906 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d46862, d321906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46862, d321906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46863 q = 2) : d367710 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d46863, d367710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46863, d367710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47235 q = 2) : d326618 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d47235, d326618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47235, d326618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38667 q selected
  have h12 (q : Pattern) (selected : d47236 q = 2) : d326619 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d47236, d326619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47236, d326619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d47237 q = 2) : d326620 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d47237, d326620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47237, d326620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d47238 q = 2) : d326621 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47238, d326621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47238, d326621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d47239 q = 2) : d367711 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47239, d367711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d47239, d367711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d47240 q = 2) : d367712 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47240, d367712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d47240, d367712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro38669 (p : Pattern) (selected : d47246 p = 2) : d367718 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47241 q = 2) : d367713 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47241, d367713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38668 q selected
    | true =>
      simp only [d47241, d367713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47242 q = 2) : d367714 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47242, d367714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47242, d367714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47243 q = 2) : d367715 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47243, d367715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47243, d367715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47244 q = 2) : d367716 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47244, d367716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47244, d367716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47245 q = 2) : d367717 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47245, d367717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47245, d367717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47246 q = 2) : d367718 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47246, d367718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47246, d367718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38670 (p : Pattern) (selected : d47252 p = 2) : d367724 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47247 q = 2) : d367719 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47247, d367719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38669 q selected
    | true =>
      simp only [d47247, d367719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47248 q = 2) : d367720 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47248, d367720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47248, d367720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47249 q = 2) : d367721 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47249, d367721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47249, d367721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47250 q = 2) : d367722 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47250, d367722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47250, d367722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47251 q = 2) : d367723 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47251, d367723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47251, d367723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47252 q = 2) : d367724 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47252, d367724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47252, d367724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38671 (p : Pattern) (selected : d47258 p = 2) : d367730 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47253 q = 2) : d367725 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47253, d367725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38670 q selected
    | true =>
      simp only [d47253, d367725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47254 q = 2) : d367726 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47254, d367726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47254, d367726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47255 q = 2) : d367727 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47255, d367727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47255, d367727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47256 q = 2) : d367728 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47256, d367728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47256, d367728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47257 q = 2) : d367729 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47257, d367729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47257, d367729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47258 q = 2) : d367730 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47258, d367730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47258, d367730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38672 (p : Pattern) (selected : d47264 p = 2) : d367736 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47259 q = 2) : d367731 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47259, d367731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38671 q selected
    | true =>
      simp only [d47259, d367731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47260 q = 2) : d367732 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47260, d367732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47260, d367732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47261 q = 2) : d367733 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47261, d367733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47261, d367733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47262 q = 2) : d367734 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47262, d367734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47262, d367734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47263 q = 2) : d367735 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47263, d367735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47263, d367735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47264 q = 2) : d367736 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47264, d367736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47264, d367736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38673 (p : Pattern) (selected : d47270 p = 2) : d367742 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47265 q = 2) : d367737 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47265, d367737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38672 q selected
    | true =>
      simp only [d47265, d367737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47266 q = 2) : d367738 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47266, d367738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47266, d367738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47267 q = 2) : d367739 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47267, d367739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47267, d367739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47268 q = 2) : d367740 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47268, d367740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47268, d367740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47269 q = 2) : d367741 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47269, d367741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47269, d367741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47270 q = 2) : d367742 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47270, d367742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47270, d367742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38674 (p : Pattern) (selected : d47276 p = 2) : d367748 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47271 q = 2) : d367743 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47271, d367743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38673 q selected
    | true =>
      simp only [d47271, d367743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47272 q = 2) : d367744 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47272, d367744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47272, d367744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47273 q = 2) : d367745 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47273, d367745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47273, d367745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47274 q = 2) : d367746 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47274, d367746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47274, d367746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47275 q = 2) : d367747 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47275, d367747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47275, d367747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47276 q = 2) : d367748 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47276, d367748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47276, d367748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38675 (p : Pattern) (selected : d47282 p = 2) : d367754 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47277 q = 2) : d367749 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47277, d367749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38674 q selected
    | true =>
      simp only [d47277, d367749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47278 q = 2) : d367750 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47278, d367750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47278, d367750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47279 q = 2) : d367751 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47279, d367751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47279, d367751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47280 q = 2) : d367752 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47280, d367752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47280, d367752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47281 q = 2) : d367753 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47281, d367753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47281, d367753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47282 q = 2) : d367754 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47282, d367754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47282, d367754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38676 (p : Pattern) (selected : d367986 p = 0) : d368770 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d13 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14 q = 0) : d51866 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1084 q = 0) : d52665 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, d52665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1084, d52665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d217973 q = 0) : d220155 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d217973, d220155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d217973, d220155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d367986 q = 0) : d368770 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d367986, d368770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d367986, d368770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38677 (p : Pattern) (selected : d367991 p = 0) : d368775 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d367987 q = 0) : d368771 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d367987, d368771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d367987, d368771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38676 q selected
  have h2 (q : Pattern) (selected : d367988 q = 0) : d368772 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d367988, d368772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d367988, d368772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d367989 q = 0) : d368773 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d367989, d368773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d367989, d368773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d367990 q = 0) : d368774 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d367990, d368774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d367990, d368774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d367991 q = 0) : d368775 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d367991, d368775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d367991, d368775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro38678 (p : Pattern) (selected : d367997 p = 0) : d368781 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d367987 q = 0) : d368771 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d367987, d368771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d367987, d368771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38676 q selected
  have h2 (q : Pattern) (selected : d367988 q = 0) : d368772 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d367988, d368772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d367988, d368772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d367989 q = 0) : d368773 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d367989, d368773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d367989, d368773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d367990 q = 0) : d368774 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d367990, d368774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d367990, d368774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218042 q = 0) : d220224 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218042, d220224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218042, d220224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21194 q selected
  have h6 (q : Pattern) (selected : d218043 q = 0) : d220225 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218043, d220225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218043, d220225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d216732 q = 0) : d219221 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d216732, d219221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21194 q selected
    | true =>
      simp only [d216732, d219221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d216733 q = 0) : d219222 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d216733, d219222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d216733, d219222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d218044 q = 0) : d220226 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d218044, d220226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218044, d220226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d218045 q = 0) : d220227 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d218045, d220227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218045, d220227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d367997 q = 0) : d368781 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d367997, d368781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d367997, d368781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38679 (p : Pattern) (selected : d368003 p = 0) : d368787 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d367992 q = 0) : d368776 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d367992, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38677 q selected
    | true =>
      simp only [d367992, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d367993 q = 0) : d368777 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d367993, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d367993, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d367994 q = 0) : d368778 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d367994, d368778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d367994, d368778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d367995 q = 0) : d368779 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d367995, d368779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d367995, d368779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d367996 q = 0) : d368780 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d367996, d368780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d367996, d368780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d367998 q = 0) : d368782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d367998, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38678 q selected
    | true =>
      simp only [d367998, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d367999 q = 0) : d368783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d367999, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d367999, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368000 q = 0) : d368784 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368000, d368784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368000, d368784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d368001 q = 0) : d368785 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368001, d368785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368001, d368785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d368002 q = 0) : d368786 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368002, d368786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368002, d368786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368003 q = 0) : d368787 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368003, d368787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368003, d368787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38680 (p : Pattern) (selected : d368005 p = 0) : d368789 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d367992 q = 0) : d368776 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d367992, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38677 q selected
    | true =>
      simp only [d367992, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d367993 q = 0) : d368777 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d367993, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d367993, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d367994 q = 0) : d368778 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d367994, d368778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d367994, d368778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d367995 q = 0) : d368779 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d367995, d368779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d367995, d368779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d367998 q = 0) : d368782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d367998, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38678 q selected
    | true =>
      simp only [d367998, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d367999 q = 0) : d368783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d367999, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d367999, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368000 q = 0) : d368784 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368000, d368784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368000, d368784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368001 q = 0) : d368785 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368001, d368785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368001, d368785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368002 q = 0) : d368786 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368002, d368786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368002, d368786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368004 q = 0) : d368788 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368004, d368788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368004, d368788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368005 q = 0) : d368789 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368005, d368789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368005, d368789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38681 (p : Pattern) (selected : d368009 p = 0) : d368793 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d367998 q = 0) : d368782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d367998, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38678 q selected
    | true =>
      simp only [d367998, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d367999 q = 0) : d368783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d367999, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d367999, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368000 q = 0) : d368784 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368000, d368784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368000, d368784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368001 q = 0) : d368785 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368001, d368785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368001, d368785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368004 q = 0) : d368788 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368004, d368788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368004, d368788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d218047 q = 0) : d220229 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218047, d220229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21440 q selected
    | true =>
      simp only [d218047, d220229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218048 q = 0) : d220230 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218048, d220230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218048, d220230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218049 q = 0) : d220231 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218049, d220231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218049, d220231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d218050 q = 0) : d220232 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218050, d220232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218050, d220232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d218051 q = 0) : d220233 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218051, d220233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218051, d220233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368009 q = 0) : d368793 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368009, d368793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368009, d368793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38682 (p : Pattern) (selected : d368016 p = 0) : d368800 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368006 q = 0) : d368790 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368006, d368790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38679 q selected
    | true =>
      simp only [d368006, d368790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38680 q selected
  have h2 (q : Pattern) (selected : d368007 q = 0) : d368791 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368007, d368791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368007, d368791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368008 q = 0) : d368792 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368008, d368792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368008, d368792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368010 q = 0) : d368794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368010, d368794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38680 q selected
    | true =>
      simp only [d368010, d368794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38681 q selected
  have h5 (q : Pattern) (selected : d368011 q = 0) : d368795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368011, d368795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368011, d368795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368012 q = 0) : d368796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368012, d368796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368012, d368796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368013 q = 0) : d368797 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368013, d368797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368013, d368797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368014 q = 0) : d368798 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368014, d368798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368014, d368798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368015 q = 0) : d368799 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368015, d368799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368015, d368799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368016 q = 0) : d368800 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368016, d368800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368016, d368800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38683 (p : Pattern) (selected : d368020 p = 0) : d368804 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368010 q = 0) : d368794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368010, d368794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38680 q selected
    | true =>
      simp only [d368010, d368794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38681 q selected
  have h2 (q : Pattern) (selected : d368011 q = 0) : d368795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368011, d368795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368011, d368795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368012 q = 0) : d368796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368012, d368796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368012, d368796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368014 q = 0) : d368798 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368014, d368798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368014, d368798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368019 q = 0) : d368803 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368019, d368803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368019, d368803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368020 q = 0) : d368804 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368020, d368804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368020, d368804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38684 (p : Pattern) (selected : d368026 p = 0) : d368810 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368017 q = 0) : d368801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368017, d368801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38682 q selected
    | true =>
      simp only [d368017, d368801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368018 q = 0) : d368802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368018, d368802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368018, d368802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368021 q = 0) : d368805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38683 q selected
    | true =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368022 q = 0) : d368806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368023 q = 0) : d368807 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368023, d368807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368023, d368807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368024 q = 0) : d368808 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368024, d368808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368024, d368808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368025 q = 0) : d368809 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368025, d368809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368025, d368809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368026 q = 0) : d368810 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368026, d368810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368026, d368810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38685 (p : Pattern) (selected : d368030 p = 0) : d368814 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368021 q = 0) : d368805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38683 q selected
    | true =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368022 q = 0) : d368806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368027 q = 0) : d368811 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368027, d368811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368027, d368811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368028 q = 0) : d368812 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368028, d368812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368028, d368812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368029 q = 0) : d368813 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368029, d368813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368029, d368813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368030 q = 0) : d368814 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368030, d368814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368030, d368814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38686 (p : Pattern) (selected : d368036 p = 0) : d368820 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368031 q = 0) : d368815 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368031, d368815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38684 q selected
    | true =>
      simp only [d368031, d368815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38685 q selected
  have h2 (q : Pattern) (selected : d368032 q = 0) : d368816 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368032, d368816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368032, d368816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368033 q = 0) : d368817 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368033, d368817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368033, d368817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368034 q = 0) : d368818 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368034, d368818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368034, d368818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368035 q = 0) : d368819 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368035, d368819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368035, d368819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368036 q = 0) : d368820 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368036, d368820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368036, d368820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38687 (p : Pattern) (selected : d368039 p = 0) : d368823 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368017 q = 0) : d368801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368017, d368801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38682 q selected
    | true =>
      simp only [d368017, d368801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368018 q = 0) : d368802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368018, d368802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368018, d368802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368021 q = 0) : d368805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38683 q selected
    | true =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368022 q = 0) : d368806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368023 q = 0) : d368807 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368023, d368807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368023, d368807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368024 q = 0) : d368808 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368024, d368808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368024, d368808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368025 q = 0) : d368809 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368025, d368809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368025, d368809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368039 q = 0) : d368823 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368039, d368823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368039, d368823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38688 (p : Pattern) (selected : d368040 p = 0) : d368824 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368021 q = 0) : d368805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38683 q selected
    | true =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368022 q = 0) : d368806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368027 q = 0) : d368811 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368027, d368811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368027, d368811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368028 q = 0) : d368812 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368028, d368812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368028, d368812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368029 q = 0) : d368813 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368029, d368813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368029, d368813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368040 q = 0) : d368824 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368040, d368824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368040, d368824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38689 (p : Pattern) (selected : d368046 p = 0) : d368830 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368031 q = 0) : d368815 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368031, d368815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38684 q selected
    | true =>
      simp only [d368031, d368815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38685 q selected
  have h2 (q : Pattern) (selected : d368032 q = 0) : d368816 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368032, d368816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368032, d368816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368033 q = 0) : d368817 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368033, d368817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368033, d368817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368034 q = 0) : d368818 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368034, d368818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368034, d368818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368035 q = 0) : d368819 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368035, d368819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368035, d368819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368041 q = 0) : d368825 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368041, d368825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38687 q selected
    | true =>
      simp only [d368041, d368825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38688 q selected
  have h7 (q : Pattern) (selected : d368042 q = 0) : d368826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368042, d368826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368042, d368826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368043 q = 0) : d368827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368043, d368827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368043, d368827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368044 q = 0) : d368828 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368044, d368828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368044, d368828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368045 q = 0) : d368829 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368045, d368829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368045, d368829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368046 q = 0) : d368830 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368046, d368830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368046, d368830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38690 (p : Pattern) (selected : d368051 p = 0) : d368835 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368017 q = 0) : d368801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368017, d368801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38682 q selected
    | true =>
      simp only [d368017, d368801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368018 q = 0) : d368802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368018, d368802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368018, d368802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368021 q = 0) : d368805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38683 q selected
    | true =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368022 q = 0) : d368806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368023 q = 0) : d368807 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368023, d368807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368023, d368807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368024 q = 0) : d368808 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368024, d368808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368024, d368808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368050 q = 0) : d368834 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368050, d368834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368050, d368834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368051 q = 0) : d368835 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368051, d368835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368051, d368835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38691 (p : Pattern) (selected : d368053 p = 0) : d368837 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368021 q = 0) : d368805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38683 q selected
    | true =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368022 q = 0) : d368806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368027 q = 0) : d368811 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368027, d368811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368027, d368811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368028 q = 0) : d368812 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368028, d368812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368028, d368812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368052 q = 0) : d368836 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368052, d368836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368052, d368836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368053 q = 0) : d368837 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368053, d368837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368053, d368837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38692 (p : Pattern) (selected : d368060 p = 0) : d368844 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368017 q = 0) : d368801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368017, d368801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38682 q selected
    | true =>
      simp only [d368017, d368801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368018 q = 0) : d368802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368018, d368802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368018, d368802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368021 q = 0) : d368805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38683 q selected
    | true =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368022 q = 0) : d368806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368023 q = 0) : d368807 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368023, d368807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368023, d368807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368058 q = 0) : d368842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368058, d368842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368058, d368842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368059 q = 0) : d368843 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368059, d368843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368059, d368843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368060 q = 0) : d368844 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368060, d368844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368060, d368844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38693 (p : Pattern) (selected : d368063 p = 0) : d368847 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368021 q = 0) : d368805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38683 q selected
    | true =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368022 q = 0) : d368806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368027 q = 0) : d368811 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368027, d368811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368027, d368811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368061 q = 0) : d368845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368061, d368845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368061, d368845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368062 q = 0) : d368846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368062, d368846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368062, d368846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368063 q = 0) : d368847 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368063, d368847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368063, d368847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38694 (p : Pattern) (selected : d368067 p = 0) : d368851 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d367992 q = 0) : d368776 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d367992, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38677 q selected
    | true =>
      simp only [d367992, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d367993 q = 0) : d368777 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d367993, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d367993, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d367994 q = 0) : d368778 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d367994, d368778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d367994, d368778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d367995 q = 0) : d368779 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d367995, d368779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d367995, d368779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d367996 q = 0) : d368780 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d367996, d368780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d367996, d368780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368067 q = 0) : d368851 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368067, d368851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368067, d368851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38695 (p : Pattern) (selected : d368073 p = 0) : d368857 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368068 q = 0) : d368852 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368068, d368852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38694 q selected
    | true =>
      simp only [d368068, d368852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38679 q selected
  have h2 (q : Pattern) (selected : d368069 q = 0) : d368853 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368069, d368853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368069, d368853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368070 q = 0) : d368854 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368070, d368854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368070, d368854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368006 q = 0) : d368790 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368006, d368790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38679 q selected
    | true =>
      simp only [d368006, d368790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38680 q selected
  have h5 (q : Pattern) (selected : d368007 q = 0) : d368791 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368007, d368791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368007, d368791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368008 q = 0) : d368792 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368008, d368792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368008, d368792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368071 q = 0) : d368855 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368071, d368855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368071, d368855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368010 q = 0) : d368794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368010, d368794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38680 q selected
    | true =>
      simp only [d368010, d368794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38681 q selected
  have h9 (q : Pattern) (selected : d368011 q = 0) : d368795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368011, d368795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368011, d368795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368012 q = 0) : d368796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368012, d368796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368012, d368796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368013 q = 0) : d368797 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368013, d368797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368013, d368797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d368072 q = 0) : d368856 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368072, d368856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368072, d368856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d368073 q = 0) : d368857 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368073, d368857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368073, d368857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro38696 (p : Pattern) (selected : d368079 p = 0) : d368863 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368074 q = 0) : d368858 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368074, d368858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38695 q selected
    | true =>
      simp only [d368074, d368858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368075 q = 0) : d368859 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368075, d368859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368075, d368859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368017 q = 0) : d368801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368017, d368801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38682 q selected
    | true =>
      simp only [d368017, d368801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368018 q = 0) : d368802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368018, d368802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368018, d368802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368076 q = 0) : d368860 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368076, d368860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368076, d368860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368077 q = 0) : d368861 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368077, d368861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368077, d368861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368078 q = 0) : d368862 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368078, d368862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368078, d368862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368079 q = 0) : d368863 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368079, d368863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368079, d368863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38697 (p : Pattern) (selected : d368081 p = 0) : d368770 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d158 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d159 q = 0) : d51866 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d159, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1233 q = 0) : d52665 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1233, d52665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1233, d52665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d218177 q = 0) : d220155 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d218177, d220155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218177, d220155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368081 q = 0) : d368770 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d368081, d368770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368081, d368770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38698 (p : Pattern) (selected : d368086 p = 0) : d368775 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368082 q = 0) : d368771 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d368082, d368771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368082, d368771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38697 q selected
  have h2 (q : Pattern) (selected : d368083 q = 0) : d368772 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d368083, d368772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368083, d368772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368084 q = 0) : d368773 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d368084, d368773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368084, d368773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368085 q = 0) : d368774 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d368085, d368774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368085, d368774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368086 q = 0) : d368775 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d368086, d368775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368086, d368775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro38699 (p : Pattern) (selected : d368092 p = 0) : d368781 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368082 q = 0) : d368771 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d368082, d368771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368082, d368771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38697 q selected
  have h2 (q : Pattern) (selected : d368083 q = 0) : d368772 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d368083, d368772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368083, d368772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368084 q = 0) : d368773 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d368084, d368773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368084, d368773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368085 q = 0) : d368774 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d368085, d368774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368085, d368774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218248 q = 0) : d220224 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218248, d220224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218248, d220224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21217 q selected
  have h6 (q : Pattern) (selected : d218249 q = 0) : d220225 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218249, d220225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218249, d220225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d216868 q = 0) : d219221 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d216868, d219221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21217 q selected
    | true =>
      simp only [d216868, d219221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d216869 q = 0) : d219222 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d216869, d219222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d216869, d219222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d218250 q = 0) : d220226 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d218250, d220226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218250, d220226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d218251 q = 0) : d220227 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d218251, d220227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218251, d220227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368092 q = 0) : d368781 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d368092, d368781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368092, d368781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38700 (p : Pattern) (selected : d368098 p = 0) : d368787 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368087 q = 0) : d368776 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368087, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38698 q selected
    | true =>
      simp only [d368087, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368088 q = 0) : d368777 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368088, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368088, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368089 q = 0) : d368778 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368089, d368778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368089, d368778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368090 q = 0) : d368779 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368090, d368779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368090, d368779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368091 q = 0) : d368780 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368091, d368780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368091, d368780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368093 q = 0) : d368782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368093, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38699 q selected
    | true =>
      simp only [d368093, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368094 q = 0) : d368783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368094, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368094, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368095 q = 0) : d368784 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368095, d368784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368095, d368784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d368096 q = 0) : d368785 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368096, d368785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368096, d368785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d368097 q = 0) : d368786 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368097, d368786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368097, d368786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368098 q = 0) : d368787 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368098, d368787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368098, d368787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38701 (p : Pattern) (selected : d368100 p = 0) : d368789 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368087 q = 0) : d368776 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368087, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38698 q selected
    | true =>
      simp only [d368087, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368088 q = 0) : d368777 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368088, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368088, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368089 q = 0) : d368778 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368089, d368778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368089, d368778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368090 q = 0) : d368779 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368090, d368779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368090, d368779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368093 q = 0) : d368782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368093, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38699 q selected
    | true =>
      simp only [d368093, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368094 q = 0) : d368783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368094, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368094, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368095 q = 0) : d368784 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368095, d368784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368095, d368784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368096 q = 0) : d368785 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368096, d368785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368096, d368785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368097 q = 0) : d368786 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368097, d368786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368097, d368786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368099 q = 0) : d368788 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368099, d368788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368099, d368788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368100 q = 0) : d368789 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368100, d368789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368100, d368789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38702 (p : Pattern) (selected : d368104 p = 0) : d368793 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368093 q = 0) : d368782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368093, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38699 q selected
    | true =>
      simp only [d368093, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368094 q = 0) : d368783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368094, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368094, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368095 q = 0) : d368784 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368095, d368784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368095, d368784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368096 q = 0) : d368785 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368096, d368785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368096, d368785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368099 q = 0) : d368788 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368099, d368788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368099, d368788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d218253 q = 0) : d220229 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218253, d220229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21481 q selected
    | true =>
      simp only [d218253, d220229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218254 q = 0) : d220230 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218254, d220230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218254, d220230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218255 q = 0) : d220231 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218255, d220231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218255, d220231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d218256 q = 0) : d220232 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218256, d220232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218256, d220232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d218257 q = 0) : d220233 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218257, d220233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218257, d220233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368104 q = 0) : d368793 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368104, d368793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368104, d368793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38703 (p : Pattern) (selected : d368111 p = 0) : d368800 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368101 q = 0) : d368790 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368101, d368790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38700 q selected
    | true =>
      simp only [d368101, d368790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38701 q selected
  have h2 (q : Pattern) (selected : d368102 q = 0) : d368791 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368102, d368791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368102, d368791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368103 q = 0) : d368792 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368103, d368792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368103, d368792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368105 q = 0) : d368794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368105, d368794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38701 q selected
    | true =>
      simp only [d368105, d368794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38702 q selected
  have h5 (q : Pattern) (selected : d368106 q = 0) : d368795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368106, d368795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368106, d368795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368107 q = 0) : d368796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368107, d368796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368107, d368796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368108 q = 0) : d368797 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368108, d368797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368108, d368797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368109 q = 0) : d368798 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368109, d368798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368109, d368798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368110 q = 0) : d368799 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368110, d368799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368110, d368799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368111 q = 0) : d368800 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368111, d368800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368111, d368800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38704 (p : Pattern) (selected : d368115 p = 0) : d368804 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368105 q = 0) : d368794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368105, d368794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38701 q selected
    | true =>
      simp only [d368105, d368794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38702 q selected
  have h2 (q : Pattern) (selected : d368106 q = 0) : d368795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368106, d368795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368106, d368795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368107 q = 0) : d368796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368107, d368796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368107, d368796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368109 q = 0) : d368798 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368109, d368798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368109, d368798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368114 q = 0) : d368803 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368114, d368803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368114, d368803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368115 q = 0) : d368804 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368115, d368804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368115, d368804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38705 (p : Pattern) (selected : d368121 p = 0) : d368810 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368112 q = 0) : d368801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368112, d368801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38703 q selected
    | true =>
      simp only [d368112, d368801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368113 q = 0) : d368802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368113, d368802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368113, d368802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368116 q = 0) : d368805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368116, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38704 q selected
    | true =>
      simp only [d368116, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368117 q = 0) : d368806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368117, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368117, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368118 q = 0) : d368807 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368118, d368807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368118, d368807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368119 q = 0) : d368808 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368119, d368808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368119, d368808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368120 q = 0) : d368809 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368120, d368809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368120, d368809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368121 q = 0) : d368810 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368121, d368810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368121, d368810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38706 (p : Pattern) (selected : d368125 p = 0) : d368814 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368116 q = 0) : d368805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368116, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38704 q selected
    | true =>
      simp only [d368116, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368117 q = 0) : d368806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368117, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368117, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368122 q = 0) : d368811 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368122, d368811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368122, d368811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368123 q = 0) : d368812 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368123, d368812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368123, d368812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368124 q = 0) : d368813 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368124, d368813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368124, d368813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368125 q = 0) : d368814 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368125, d368814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368125, d368814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38707 (p : Pattern) (selected : d368128 p = 0) : d368866 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d367987 q = 0) : d368771 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d367987, d368771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d367987, d368771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38676 q selected
  have h2 (q : Pattern) (selected : d367988 q = 0) : d368772 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d367988, d368772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d367988, d368772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d367989 q = 0) : d368773 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d367989, d368773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d367989, d368773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d367990 q = 0) : d368774 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d367990, d368774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d367990, d368774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368128 q = 0) : d368866 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d368128, d368866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368128, d368866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro38708 (p : Pattern) (selected : d368134 p = 0) : d368872 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d367992 q = 0) : d368776 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d367992, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38677 q selected
    | true =>
      simp only [d367992, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d367993 q = 0) : d368777 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d367993, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d367993, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d367994 q = 0) : d368778 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d367994, d368778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d367994, d368778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d367995 q = 0) : d368779 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d367995, d368779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d367995, d368779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d367998 q = 0) : d368782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d367998, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38678 q selected
    | true =>
      simp only [d367998, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d367999 q = 0) : d368783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d367999, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d367999, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368000 q = 0) : d368784 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368000, d368784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368000, d368784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368001 q = 0) : d368785 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368001, d368785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368001, d368785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368002 q = 0) : d368786 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368002, d368786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368002, d368786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368129 q = 0) : d368867 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368129, d368867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38707 q selected
    | true =>
      simp only [d368129, d368867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368130 q = 0) : d368868 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368130, d368868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368130, d368868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d368131 q = 0) : d368869 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368131, d368869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368131, d368869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d368132 q = 0) : d368870 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368132, d368870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368132, d368870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d368133 q = 0) : d368871 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368133, d368871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d368133, d368871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d368134 q = 0) : d368872 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368134, d368872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368134, d368872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38709 (p : Pattern) (selected : d368135 p = 0) : d368873 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368129 q = 0) : d368867 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368129, d368867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38707 q selected
    | true =>
      simp only [d368129, d368867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368130 q = 0) : d368868 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368130, d368868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368130, d368868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368131 q = 0) : d368869 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368131, d368869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368131, d368869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368132 q = 0) : d368870 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368132, d368870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368132, d368870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368133 q = 0) : d368871 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368133, d368871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368133, d368871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368135 q = 0) : d368873 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368135, d368873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368135, d368873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38710 (p : Pattern) (selected : d368141 p = 0) : d368879 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368006 q = 0) : d368790 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368006, d368790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38679 q selected
    | true =>
      simp only [d368006, d368790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38680 q selected
  have h2 (q : Pattern) (selected : d368007 q = 0) : d368791 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368007, d368791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368007, d368791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368008 q = 0) : d368792 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368008, d368792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368008, d368792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368010 q = 0) : d368794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368010, d368794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38680 q selected
    | true =>
      simp only [d368010, d368794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38681 q selected
  have h5 (q : Pattern) (selected : d368011 q = 0) : d368795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368011, d368795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368011, d368795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368012 q = 0) : d368796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368012, d368796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368012, d368796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368013 q = 0) : d368797 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368013, d368797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368013, d368797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368136 q = 0) : d368874 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368136, d368874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38708 q selected
    | true =>
      simp only [d368136, d368874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38709 q selected
  have h9 (q : Pattern) (selected : d368137 q = 0) : d368875 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368137, d368875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368137, d368875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368138 q = 0) : d368876 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368138, d368876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368138, d368876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368139 q = 0) : d368877 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368139, d368877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368139, d368877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d368140 q = 0) : d368878 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368140, d368878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368140, d368878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d368141 q = 0) : d368879 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368141, d368879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368141, d368879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro38711 (p : Pattern) (selected : d368147 p = 0) : d368885 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368142 q = 0) : d368880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368142, d368880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38710 q selected
    | true =>
      simp only [d368142, d368880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368143 q = 0) : d368881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368143, d368881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368143, d368881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368144 q = 0) : d368882 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368144, d368882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368144, d368882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368145 q = 0) : d368883 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368145, d368883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368145, d368883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368146 q = 0) : d368884 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368146, d368884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368146, d368884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368147 q = 0) : d368885 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368147, d368885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368147, d368885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38712 (p : Pattern) (selected : d368153 p = 0) : d368891 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368054 q = 0) : d368838 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368054, d368838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38690 q selected
    | true =>
      simp only [d368054, d368838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38691 q selected
  have h2 (q : Pattern) (selected : d368055 q = 0) : d368839 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368055, d368839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368055, d368839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368056 q = 0) : d368840 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368056, d368840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368056, d368840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368057 q = 0) : d368841 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368057, d368841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368057, d368841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368064 q = 0) : d368848 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368064, d368848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38692 q selected
    | true =>
      simp only [d368064, d368848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38693 q selected
  have h6 (q : Pattern) (selected : d368065 q = 0) : d368849 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368065, d368849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368065, d368849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368066 q = 0) : d368850 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368066, d368850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368066, d368850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368080 q = 0) : d368864 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368080, d368864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38696 q selected
    | true =>
      simp only [d368080, d368864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38684 q selected
  have h9 (q : Pattern) (selected : d368126 q = 0) : d368815 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368126, d368815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38705 q selected
    | true =>
      simp only [d368126, d368815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38706 q selected
  have h10 (q : Pattern) (selected : d368127 q = 0) : d368865 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368127, d368865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368127, d368865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368148 q = 0) : d368886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368148, d368886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38711 q selected
    | true =>
      simp only [d368148, d368886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d368149 q = 0) : d368887 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368149, d368887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d368149, d368887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d368150 q = 0) : d368888 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368150, d368888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368150, d368888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d368151 q = 0) : d368889 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368151, d368889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368151, d368889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d368152 q = 0) : d368890 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368152, d368890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368152, d368890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d368153 q = 0) : d368891 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368153, d368891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368153, d368891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro38713 (p : Pattern) (selected : d368154 p = 0) : d368892 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368017 q = 0) : d368801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368017, d368801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38682 q selected
    | true =>
      simp only [d368017, d368801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368018 q = 0) : d368802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368018, d368802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368018, d368802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368021 q = 0) : d368805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38683 q selected
    | true =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368022 q = 0) : d368806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368023 q = 0) : d368807 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368023, d368807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368023, d368807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368024 q = 0) : d368808 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368024, d368808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368024, d368808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368050 q = 0) : d368834 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368050, d368834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368050, d368834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368154 q = 0) : d368892 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368154, d368892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368154, d368892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38714 (p : Pattern) (selected : d368155 p = 0) : d368893 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368021 q = 0) : d368805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38683 q selected
    | true =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368022 q = 0) : d368806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368027 q = 0) : d368811 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368027, d368811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368027, d368811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368028 q = 0) : d368812 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368028, d368812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368028, d368812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368052 q = 0) : d368836 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368052, d368836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368052, d368836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368155 q = 0) : d368893 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368155, d368893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368155, d368893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38715 (p : Pattern) (selected : d368160 p = 0) : d368898 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368017 q = 0) : d368801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368017, d368801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38682 q selected
    | true =>
      simp only [d368017, d368801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368018 q = 0) : d368802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368018, d368802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368018, d368802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368021 q = 0) : d368805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38683 q selected
    | true =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368022 q = 0) : d368806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368023 q = 0) : d368807 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368023, d368807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368023, d368807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368058 q = 0) : d368842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368058, d368842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368058, d368842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368059 q = 0) : d368843 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368059, d368843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368059, d368843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368160 q = 0) : d368898 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368160, d368898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368160, d368898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38716 (p : Pattern) (selected : d368161 p = 0) : d368899 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368021 q = 0) : d368805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38683 q selected
    | true =>
      simp only [d368021, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368022 q = 0) : d368806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368022, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368027 q = 0) : d368811 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368027, d368811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368027, d368811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368061 q = 0) : d368845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368061, d368845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368061, d368845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368062 q = 0) : d368846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368062, d368846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368062, d368846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368161 q = 0) : d368899 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368161, d368899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368161, d368899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38717 (p : Pattern) (selected : d368165 p = 0) : d368903 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368074 q = 0) : d368858 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368074, d368858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38695 q selected
    | true =>
      simp only [d368074, d368858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368075 q = 0) : d368859 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368075, d368859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368075, d368859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368017 q = 0) : d368801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368017, d368801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38682 q selected
    | true =>
      simp only [d368017, d368801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368018 q = 0) : d368802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368018, d368802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368018, d368802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368076 q = 0) : d368860 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368076, d368860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368076, d368860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368077 q = 0) : d368861 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368077, d368861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368077, d368861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368078 q = 0) : d368862 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368078, d368862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368078, d368862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368165 q = 0) : d368903 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368165, d368903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368165, d368903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38718 (p : Pattern) (selected : d368167 p = 0) : d368823 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368112 q = 0) : d368801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368112, d368801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38703 q selected
    | true =>
      simp only [d368112, d368801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368113 q = 0) : d368802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368113, d368802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368113, d368802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368116 q = 0) : d368805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368116, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38704 q selected
    | true =>
      simp only [d368116, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368117 q = 0) : d368806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368117, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368117, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368118 q = 0) : d368807 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368118, d368807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368118, d368807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368119 q = 0) : d368808 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368119, d368808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368119, d368808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368120 q = 0) : d368809 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368120, d368809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368120, d368809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368167 q = 0) : d368823 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368167, d368823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368167, d368823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38719 (p : Pattern) (selected : d368168 p = 0) : d368824 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368116 q = 0) : d368805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368116, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38704 q selected
    | true =>
      simp only [d368116, d368805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368117 q = 0) : d368806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368117, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368117, d368806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368122 q = 0) : d368811 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368122, d368811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368122, d368811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368123 q = 0) : d368812 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368123, d368812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368123, d368812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368124 q = 0) : d368813 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368124, d368813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368124, d368813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368168 q = 0) : d368824 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368168, d368824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368168, d368824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38720 (p : Pattern) (selected : d368171 p = 0) : d368906 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368142 q = 0) : d368880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368142, d368880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38710 q selected
    | true =>
      simp only [d368142, d368880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368143 q = 0) : d368881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368143, d368881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368143, d368881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368144 q = 0) : d368882 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368144, d368882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368144, d368882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368145 q = 0) : d368883 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368145, d368883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368145, d368883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368146 q = 0) : d368884 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368146, d368884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368146, d368884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368171 q = 0) : d368906 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368171, d368906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368171, d368906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38721 (p : Pattern) (selected : d368177 p = 0) : d368912 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368054 q = 0) : d368838 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368054, d368838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38690 q selected
    | true =>
      simp only [d368054, d368838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38691 q selected
  have h2 (q : Pattern) (selected : d368055 q = 0) : d368839 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368055, d368839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368055, d368839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368056 q = 0) : d368840 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368056, d368840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368056, d368840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368057 q = 0) : d368841 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368057, d368841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368057, d368841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368064 q = 0) : d368848 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368064, d368848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38692 q selected
    | true =>
      simp only [d368064, d368848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38693 q selected
  have h6 (q : Pattern) (selected : d368065 q = 0) : d368849 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368065, d368849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368065, d368849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368066 q = 0) : d368850 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368066, d368850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368066, d368850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368080 q = 0) : d368864 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368080, d368864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38696 q selected
    | true =>
      simp only [d368080, d368864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38684 q selected
  have h9 (q : Pattern) (selected : d368126 q = 0) : d368815 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368126, d368815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38705 q selected
    | true =>
      simp only [d368126, d368815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38706 q selected
  have h10 (q : Pattern) (selected : d368127 q = 0) : d368865 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368127, d368865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368127, d368865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368148 q = 0) : d368886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368148, d368886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38711 q selected
    | true =>
      simp only [d368148, d368886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d368149 q = 0) : d368887 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368149, d368887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d368149, d368887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d368150 q = 0) : d368888 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368150, d368888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368150, d368888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d368151 q = 0) : d368889 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368151, d368889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368151, d368889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d368152 q = 0) : d368890 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368152, d368890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368152, d368890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d368156 q = 0) : d368894 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368156, d368894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38713 q selected
    | true =>
      simp only [d368156, d368894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38714 q selected
  have h17 (q : Pattern) (selected : d368157 q = 0) : d368895 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368157, d368895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368157, d368895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d368158 q = 0) : d368896 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368158, d368896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d368158, d368896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d368159 q = 0) : d368897 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368159, d368897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368159, d368897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d368162 q = 0) : d368900 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368162, d368900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38715 q selected
    | true =>
      simp only [d368162, d368900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38716 q selected
  have h21 (q : Pattern) (selected : d368163 q = 0) : d368901 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368163, d368901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368163, d368901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d368164 q = 0) : d368902 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368164, d368902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d368164, d368902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d368166 q = 0) : d368904 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368166, d368904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38717 q selected
    | true =>
      simp only [d368166, d368904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38687 q selected
  have h24 (q : Pattern) (selected : d368169 q = 0) : d368825 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368169, d368825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38718 q selected
    | true =>
      simp only [d368169, d368825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38719 q selected
  have h25 (q : Pattern) (selected : d368170 q = 0) : d368905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368170, d368905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d368170, d368905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d368172 q = 0) : d368907 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368172, d368907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38720 q selected
    | true =>
      simp only [d368172, d368907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d368173 q = 0) : d368908 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368173, d368908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d368173, d368908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d368174 q = 0) : d368909 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368174, d368909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d368174, d368909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d368175 q = 0) : d368910 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368175, d368910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d368175, d368910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d368176 q = 0) : d368911 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368176, d368911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d368176, d368911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d368177 q = 0) : d368912 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368177, d368912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d368177, d368912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro38722 (p : Pattern) (selected : d368184 p = 0) : d368919 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368031 q = 0) : d368815 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368031, d368815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38684 q selected
    | true =>
      simp only [d368031, d368815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38685 q selected
  have h2 (q : Pattern) (selected : d368032 q = 0) : d368816 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368032, d368816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368032, d368816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368033 q = 0) : d368817 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368033, d368817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368033, d368817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368034 q = 0) : d368818 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368034, d368818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368034, d368818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368035 q = 0) : d368819 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368035, d368819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368035, d368819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368179 q = 0) : d368914 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368179, d368914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38685 q selected
    | true =>
      simp only [d368179, d368914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368180 q = 0) : d368915 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368180, d368915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368180, d368915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368181 q = 0) : d368916 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368181, d368916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368181, d368916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368182 q = 0) : d368917 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368182, d368917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368182, d368917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368183 q = 0) : d368918 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368183, d368918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368183, d368918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368184 q = 0) : d368919 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368184, d368919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368184, d368919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38723 (p : Pattern) (selected : d368190 p = 0) : d368925 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368179 q = 0) : d368914 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368179, d368914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38685 q selected
    | true =>
      simp only [d368179, d368914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368180 q = 0) : d368915 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368180, d368915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368180, d368915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368181 q = 0) : d368916 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368181, d368916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368181, d368916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368182 q = 0) : d368917 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368182, d368917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368182, d368917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368183 q = 0) : d368918 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368183, d368918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368183, d368918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368185 q = 0) : d368920 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368185, d368920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38688 q selected
    | true =>
      simp only [d368185, d368920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368186 q = 0) : d368921 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368186, d368921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368186, d368921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368187 q = 0) : d368922 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368187, d368922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368187, d368922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368188 q = 0) : d368923 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368188, d368923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368188, d368923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368189 q = 0) : d368924 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368189, d368924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368189, d368924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368190 q = 0) : d368925 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368190, d368925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368190, d368925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38724 (p : Pattern) (selected : d368197 p = 0) : d368932 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368166 q = 0) : d368904 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368166, d368904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38717 q selected
    | true =>
      simp only [d368166, d368904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38687 q selected
  have h2 (q : Pattern) (selected : d368169 q = 0) : d368825 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368169, d368825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38718 q selected
    | true =>
      simp only [d368169, d368825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38719 q selected
  have h3 (q : Pattern) (selected : d368170 q = 0) : d368905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368170, d368905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368170, d368905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368172 q = 0) : d368907 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368172, d368907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38720 q selected
    | true =>
      simp only [d368172, d368907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368173 q = 0) : d368908 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368173, d368908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368173, d368908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368174 q = 0) : d368909 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368174, d368909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368174, d368909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368195 q = 0) : d368930 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368195, d368930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368195, d368930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368196 q = 0) : d368931 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368196, d368931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368196, d368931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d368197 q = 0) : d368932 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368197, d368932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368197, d368932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38725 (p : Pattern) (selected : d368199 p = 0) : d368934 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368185 q = 0) : d368920 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368185, d368920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38688 q selected
    | true =>
      simp only [d368185, d368920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368186 q = 0) : d368921 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368186, d368921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368186, d368921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368187 q = 0) : d368922 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368187, d368922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368187, d368922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368188 q = 0) : d368923 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368188, d368923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368188, d368923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368189 q = 0) : d368924 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368189, d368924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368189, d368924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368199 q = 0) : d368934 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368199, d368934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368199, d368934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38726 (p : Pattern) (selected : d368210 p = 0) : d368945 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368205 q = 0) : d368940 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368205, d368940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368205, d368940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38677 q selected
  have h2 (q : Pattern) (selected : d367992 q = 0) : d368776 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d367992, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38677 q selected
    | true =>
      simp only [d367992, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368206 q = 0) : d368941 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368206, d368941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368206, d368941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d367993 q = 0) : d368777 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d367993, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d367993, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368207 q = 0) : d368942 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368207, d368942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368207, d368942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368208 q = 0) : d368943 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368208, d368943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368208, d368943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368209 q = 0) : d368944 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368209, d368944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368209, d368944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368210 q = 0) : d368945 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368210, d368945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368210, d368945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38727 (p : Pattern) (selected : d368216 p = 0) : d368951 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368205 q = 0) : d368940 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368205, d368940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368205, d368940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38677 q selected
  have h2 (q : Pattern) (selected : d367992 q = 0) : d368776 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d367992, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38677 q selected
    | true =>
      simp only [d367992, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368206 q = 0) : d368941 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368206, d368941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368206, d368941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d367993 q = 0) : d368777 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d367993, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d367993, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368207 q = 0) : d368942 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368207, d368942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368207, d368942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368208 q = 0) : d368943 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368208, d368943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368208, d368943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368209 q = 0) : d368944 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368209, d368944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368209, d368944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368211 q = 0) : d368946 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368211, d368946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368211, d368946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38678 q selected
  have h9 (q : Pattern) (selected : d367998 q = 0) : d368782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d367998, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38678 q selected
    | true =>
      simp only [d367998, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d368212 q = 0) : d368947 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368212, d368947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368212, d368947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d367999 q = 0) : d368783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d367999, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d367999, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d368213 q = 0) : d368948 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368213, d368948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368213, d368948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d368214 q = 0) : d368949 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368214, d368949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368214, d368949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d368215 q = 0) : d368950 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368215, d368950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368215, d368950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d368216 q = 0) : d368951 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368216, d368951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368216, d368951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38728 (p : Pattern) (selected : d368221 p = 0) : d368956 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368205 q = 0) : d368940 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368205, d368940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368205, d368940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38677 q selected
  have h2 (q : Pattern) (selected : d367992 q = 0) : d368776 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d367992, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38677 q selected
    | true =>
      simp only [d367992, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368206 q = 0) : d368941 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368206, d368941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368206, d368941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d367993 q = 0) : d368777 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d367993, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d367993, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368207 q = 0) : d368942 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368207, d368942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368207, d368942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368208 q = 0) : d368943 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368208, d368943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368208, d368943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368211 q = 0) : d368946 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368211, d368946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368211, d368946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38678 q selected
  have h8 (q : Pattern) (selected : d367998 q = 0) : d368782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d367998, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38678 q selected
    | true =>
      simp only [d367998, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368212 q = 0) : d368947 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368212, d368947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368212, d368947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d367999 q = 0) : d368783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d367999, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d367999, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368213 q = 0) : d368948 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368213, d368948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368213, d368948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d368214 q = 0) : d368949 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368214, d368949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d368214, d368949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d368215 q = 0) : d368950 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368215, d368950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368215, d368950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d368220 q = 0) : d368955 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368220, d368955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368220, d368955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d368221 q = 0) : d368956 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368221, d368956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d368221, d368956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38729 (p : Pattern) (selected : d368226 p = 0) : d368961 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368211 q = 0) : d368946 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368211, d368946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368211, d368946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38678 q selected
  have h2 (q : Pattern) (selected : d367998 q = 0) : d368782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d367998, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38678 q selected
    | true =>
      simp only [d367998, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368212 q = 0) : d368947 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368212, d368947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368212, d368947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d367999 q = 0) : d368783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d367999, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d367999, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368213 q = 0) : d368948 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368213, d368948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368213, d368948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368214 q = 0) : d368949 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368214, d368949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368214, d368949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368220 q = 0) : d368955 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368220, d368955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368220, d368955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218426 q = 0) : d220485 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218426, d220485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218426, d220485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21440 q selected
  have h9 (q : Pattern) (selected : d218047 q = 0) : d220229 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218047, d220229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21440 q selected
    | true =>
      simp only [d218047, d220229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d218427 q = 0) : d220486 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218427, d220486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218427, d220486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d218048 q = 0) : d220230 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218048, d220230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218048, d220230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d218428 q = 0) : d220487 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218428, d220487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d218428, d220487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d218429 q = 0) : d220488 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218429, d220488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d218429, d220488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d218430 q = 0) : d220489 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218430, d220489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d218430, d220489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d368226 q = 0) : d368961 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368226, d368961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368226, d368961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38730 (p : Pattern) (selected : d368232 p = 0) : d368967 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368217 q = 0) : d368952 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368217, d368952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38726 q selected
    | true =>
      simp only [d368217, d368952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38727 q selected
  have h2 (q : Pattern) (selected : d368218 q = 0) : d368953 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368218, d368953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368218, d368953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368219 q = 0) : d368954 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368219, d368954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368219, d368954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368222 q = 0) : d368957 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368222, d368957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38727 q selected
    | true =>
      simp only [d368222, d368957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38728 q selected
  have h5 (q : Pattern) (selected : d368223 q = 0) : d368958 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368223, d368958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368223, d368958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368224 q = 0) : d368959 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368224, d368959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368224, d368959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368225 q = 0) : d368960 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368225, d368960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368225, d368960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368227 q = 0) : d368962 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368227, d368962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38728 q selected
    | true =>
      simp only [d368227, d368962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38729 q selected
  have h9 (q : Pattern) (selected : d368228 q = 0) : d368963 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368228, d368963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368228, d368963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368229 q = 0) : d368964 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368229, d368964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368229, d368964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368230 q = 0) : d368965 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368230, d368965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368230, d368965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d368231 q = 0) : d368966 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368231, d368966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368231, d368966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d368232 q = 0) : d368967 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368232, d368967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368232, d368967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro38731 (p : Pattern) (selected : d368237 p = 0) : d368972 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368222 q = 0) : d368957 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368222, d368957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38727 q selected
    | true =>
      simp only [d368222, d368957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38728 q selected
  have h2 (q : Pattern) (selected : d368223 q = 0) : d368958 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368223, d368958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368223, d368958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368224 q = 0) : d368959 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368224, d368959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368224, d368959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368227 q = 0) : d368962 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368227, d368962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38728 q selected
    | true =>
      simp only [d368227, d368962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38729 q selected
  have h5 (q : Pattern) (selected : d368228 q = 0) : d368963 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368228, d368963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368228, d368963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368229 q = 0) : d368964 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368229, d368964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368229, d368964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368230 q = 0) : d368965 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368230, d368965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368230, d368965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368235 q = 0) : d368970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368235, d368970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368235, d368970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368236 q = 0) : d368971 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368236, d368971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368236, d368971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368237 q = 0) : d368972 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368237, d368972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368237, d368972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38732 (p : Pattern) (selected : d368243 p = 0) : d368978 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368233 q = 0) : d368968 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368233, d368968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38730 q selected
    | true =>
      simp only [d368233, d368968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368234 q = 0) : d368969 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368234, d368969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368234, d368969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368238 q = 0) : d368973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368238, d368973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38731 q selected
    | true =>
      simp only [d368238, d368973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368239 q = 0) : d368974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368239, d368974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368239, d368974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368240 q = 0) : d368975 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368240, d368975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368240, d368975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368241 q = 0) : d368976 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368241, d368976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368241, d368976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368242 q = 0) : d368977 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368242, d368977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368242, d368977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368243 q = 0) : d368978 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368243, d368978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368243, d368978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38733 (p : Pattern) (selected : d368245 p = 0) : d368980 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368227 q = 0) : d368962 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368227, d368962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38728 q selected
    | true =>
      simp only [d368227, d368962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38729 q selected
  have h2 (q : Pattern) (selected : d368228 q = 0) : d368963 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368228, d368963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368228, d368963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368229 q = 0) : d368964 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368229, d368964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368229, d368964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368235 q = 0) : d368970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368235, d368970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368235, d368970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368244 q = 0) : d368979 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368244, d368979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368244, d368979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368245 q = 0) : d368980 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368245, d368980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368245, d368980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38734 (p : Pattern) (selected : d368251 p = 0) : d368986 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368238 q = 0) : d368973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368238, d368973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38731 q selected
    | true =>
      simp only [d368238, d368973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368239 q = 0) : d368974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368239, d368974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368239, d368974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368246 q = 0) : d368981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368246, d368981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38733 q selected
    | true =>
      simp only [d368246, d368981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368247 q = 0) : d368982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368247, d368982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368247, d368982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368248 q = 0) : d368983 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368248, d368983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368248, d368983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368249 q = 0) : d368984 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368249, d368984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368249, d368984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368250 q = 0) : d368985 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368250, d368985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368250, d368985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368251 q = 0) : d368986 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368251, d368986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368251, d368986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38735 (p : Pattern) (selected : d368263 p = 0) : d368951 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368253 q = 0) : d368940 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368253, d368940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368253, d368940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38698 q selected
  have h2 (q : Pattern) (selected : d368087 q = 0) : d368776 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368087, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38698 q selected
    | true =>
      simp only [d368087, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368254 q = 0) : d368941 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368254, d368941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368254, d368941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368088 q = 0) : d368777 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368088, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368088, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368255 q = 0) : d368942 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368255, d368942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368255, d368942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368256 q = 0) : d368943 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368256, d368943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368256, d368943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368257 q = 0) : d368944 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368257, d368944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368257, d368944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368258 q = 0) : d368946 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368258, d368946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368258, d368946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38699 q selected
  have h9 (q : Pattern) (selected : d368093 q = 0) : d368782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368093, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38699 q selected
    | true =>
      simp only [d368093, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d368259 q = 0) : d368947 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368259, d368947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368259, d368947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368094 q = 0) : d368783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368094, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368094, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d368260 q = 0) : d368948 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368260, d368948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368260, d368948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d368261 q = 0) : d368949 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368261, d368949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368261, d368949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d368262 q = 0) : d368950 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368262, d368950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368262, d368950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d368263 q = 0) : d368951 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368263, d368951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368263, d368951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38736 (p : Pattern) (selected : d368265 p = 0) : d368956 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368253 q = 0) : d368940 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368253, d368940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368253, d368940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38698 q selected
  have h2 (q : Pattern) (selected : d368087 q = 0) : d368776 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368087, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38698 q selected
    | true =>
      simp only [d368087, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368254 q = 0) : d368941 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368254, d368941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368254, d368941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368088 q = 0) : d368777 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368088, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368088, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368255 q = 0) : d368942 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368255, d368942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368255, d368942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368256 q = 0) : d368943 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368256, d368943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368256, d368943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368258 q = 0) : d368946 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368258, d368946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368258, d368946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38699 q selected
  have h8 (q : Pattern) (selected : d368093 q = 0) : d368782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368093, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38699 q selected
    | true =>
      simp only [d368093, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368259 q = 0) : d368947 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368259, d368947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368259, d368947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368094 q = 0) : d368783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368094, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368094, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368260 q = 0) : d368948 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368260, d368948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368260, d368948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d368261 q = 0) : d368949 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368261, d368949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d368261, d368949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d368262 q = 0) : d368950 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368262, d368950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368262, d368950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d368264 q = 0) : d368955 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368264, d368955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368264, d368955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d368265 q = 0) : d368956 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368265, d368956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d368265, d368956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38737 (p : Pattern) (selected : d368269 p = 0) : d368961 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368258 q = 0) : d368946 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368258, d368946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368258, d368946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38699 q selected
  have h2 (q : Pattern) (selected : d368093 q = 0) : d368782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368093, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38699 q selected
    | true =>
      simp only [d368093, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368259 q = 0) : d368947 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368259, d368947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368259, d368947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368094 q = 0) : d368783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368094, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368094, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368260 q = 0) : d368948 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368260, d368948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368260, d368948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368261 q = 0) : d368949 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368261, d368949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368261, d368949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368264 q = 0) : d368955 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368264, d368955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368264, d368955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218501 q = 0) : d220485 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218501, d220485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218501, d220485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21481 q selected
  have h9 (q : Pattern) (selected : d218253 q = 0) : d220229 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218253, d220229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21481 q selected
    | true =>
      simp only [d218253, d220229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d218502 q = 0) : d220486 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218502, d220486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218502, d220486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d218254 q = 0) : d220230 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218254, d220230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218254, d220230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d218503 q = 0) : d220487 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218503, d220487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d218503, d220487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d218504 q = 0) : d220488 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218504, d220488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d218504, d220488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d218505 q = 0) : d220489 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218505, d220489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d218505, d220489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d368269 q = 0) : d368961 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368269, d368961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368269, d368961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38738 (p : Pattern) (selected : d368276 p = 0) : d368972 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368266 q = 0) : d368957 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368266, d368957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38735 q selected
    | true =>
      simp only [d368266, d368957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38736 q selected
  have h2 (q : Pattern) (selected : d368267 q = 0) : d368958 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368267, d368958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368267, d368958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368268 q = 0) : d368959 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368268, d368959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368268, d368959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368270 q = 0) : d368962 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368270, d368962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38736 q selected
    | true =>
      simp only [d368270, d368962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38737 q selected
  have h5 (q : Pattern) (selected : d368271 q = 0) : d368963 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368271, d368963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368271, d368963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368272 q = 0) : d368964 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368272, d368964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368272, d368964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368273 q = 0) : d368965 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368273, d368965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368273, d368965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368274 q = 0) : d368970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368274, d368970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368274, d368970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368275 q = 0) : d368971 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368275, d368971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368275, d368971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368276 q = 0) : d368972 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368276, d368972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368276, d368972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38739 (p : Pattern) (selected : d368280 p = 0) : d368980 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368270 q = 0) : d368962 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368270, d368962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38736 q selected
    | true =>
      simp only [d368270, d368962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38737 q selected
  have h2 (q : Pattern) (selected : d368271 q = 0) : d368963 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368271, d368963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368271, d368963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368272 q = 0) : d368964 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368272, d368964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368272, d368964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368274 q = 0) : d368970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368274, d368970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368274, d368970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368279 q = 0) : d368979 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368279, d368979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368279, d368979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368280 q = 0) : d368980 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368280, d368980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368280, d368980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38740 (p : Pattern) (selected : d368286 p = 0) : d368986 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368277 q = 0) : d368973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368277, d368973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38738 q selected
    | true =>
      simp only [d368277, d368973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368278 q = 0) : d368974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368278, d368974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368278, d368974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368281 q = 0) : d368981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368281, d368981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38739 q selected
    | true =>
      simp only [d368281, d368981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368282 q = 0) : d368982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368282, d368982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368282, d368982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368283 q = 0) : d368983 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368283, d368983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368283, d368983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368284 q = 0) : d368984 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368284, d368984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368284, d368984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368285 q = 0) : d368985 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368285, d368985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368285, d368985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368286 q = 0) : d368986 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368286, d368986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368286, d368986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38741 (p : Pattern) (selected : d368290 p = 0) : d368991 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368281 q = 0) : d368981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368281, d368981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38739 q selected
    | true =>
      simp only [d368281, d368981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368282 q = 0) : d368982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368282, d368982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368282, d368982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368287 q = 0) : d368988 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368287, d368988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368287, d368988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368288 q = 0) : d368989 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368288, d368989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368288, d368989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368289 q = 0) : d368990 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368289, d368990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368289, d368990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368290 q = 0) : d368991 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368290, d368991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368290, d368991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38742 (p : Pattern) (selected : d368298 p = 0) : d368999 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368205 q = 0) : d368940 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368205, d368940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368205, d368940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38677 q selected
  have h2 (q : Pattern) (selected : d367992 q = 0) : d368776 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d367992, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38677 q selected
    | true =>
      simp only [d367992, d368776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368206 q = 0) : d368941 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368206, d368941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368206, d368941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d367993 q = 0) : d368777 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d367993, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d367993, d368777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368207 q = 0) : d368942 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368207, d368942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368207, d368942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368208 q = 0) : d368943 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368208, d368943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368208, d368943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368211 q = 0) : d368946 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368211, d368946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368211, d368946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38678 q selected
  have h8 (q : Pattern) (selected : d367998 q = 0) : d368782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d367998, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38678 q selected
    | true =>
      simp only [d367998, d368782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368212 q = 0) : d368947 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368212, d368947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368212, d368947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d367999 q = 0) : d368783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d367999, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d367999, d368783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368213 q = 0) : d368948 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368213, d368948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368213, d368948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d368214 q = 0) : d368949 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368214, d368949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d368214, d368949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d368215 q = 0) : d368950 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368215, d368950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368215, d368950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d368293 q = 0) : d368994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368293, d368994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368293, d368994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38707 q selected
  have h15 (q : Pattern) (selected : d368129 q = 0) : d368867 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368129, d368867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38707 q selected
    | true =>
      simp only [d368129, d368867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d368294 q = 0) : d368995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368294, d368995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d368294, d368995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d368130 q = 0) : d368868 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368130, d368868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d368130, d368868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d368295 q = 0) : d368996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368295, d368996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d368295, d368996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d368296 q = 0) : d368997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368296, d368997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d368296, d368997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d368297 q = 0) : d368998 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368297, d368998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d368297, d368998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d368298 q = 0) : d368999 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368298, d368999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d368298, d368999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro38743 (p : Pattern) (selected : d368299 p = 0) : d369000 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368293 q = 0) : d368994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368293, d368994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368293, d368994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38707 q selected
  have h2 (q : Pattern) (selected : d368129 q = 0) : d368867 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368129, d368867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38707 q selected
    | true =>
      simp only [d368129, d368867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368294 q = 0) : d368995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368294, d368995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368294, d368995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368130 q = 0) : d368868 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368130, d368868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368130, d368868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368295 q = 0) : d368996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368295, d368996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368295, d368996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368296 q = 0) : d368997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368296, d368997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368296, d368997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368297 q = 0) : d368998 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368297, d368998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368297, d368998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368299 q = 0) : d369000 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368299, d369000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368299, d369000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38744 (p : Pattern) (selected : d368305 p = 0) : d369006 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368222 q = 0) : d368957 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368222, d368957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38727 q selected
    | true =>
      simp only [d368222, d368957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38728 q selected
  have h2 (q : Pattern) (selected : d368223 q = 0) : d368958 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368223, d368958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368223, d368958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368224 q = 0) : d368959 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368224, d368959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368224, d368959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368227 q = 0) : d368962 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368227, d368962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38728 q selected
    | true =>
      simp only [d368227, d368962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38729 q selected
  have h5 (q : Pattern) (selected : d368228 q = 0) : d368963 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368228, d368963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368228, d368963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368229 q = 0) : d368964 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368229, d368964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368229, d368964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368230 q = 0) : d368965 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368230, d368965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368230, d368965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368300 q = 0) : d369001 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368300, d369001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38742 q selected
    | true =>
      simp only [d368300, d369001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38743 q selected
  have h9 (q : Pattern) (selected : d368301 q = 0) : d369002 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368301, d369002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368301, d369002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368302 q = 0) : d369003 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368302, d369003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368302, d369003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368303 q = 0) : d369004 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368303, d369004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368303, d369004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d368304 q = 0) : d369005 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368304, d369005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368304, d369005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d368305 q = 0) : d369006 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368305, d369006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368305, d369006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro38745 (p : Pattern) (selected : d368311 p = 0) : d369012 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368306 q = 0) : d369007 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368306, d369007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38744 q selected
    | true =>
      simp only [d368306, d369007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368307 q = 0) : d369008 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368307, d369008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368307, d369008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368308 q = 0) : d369009 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368308, d369009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368308, d369009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368309 q = 0) : d369010 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368309, d369010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368309, d369010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368310 q = 0) : d369011 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368310, d369011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368310, d369011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368311 q = 0) : d369012 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368311, d369012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368311, d369012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38746 (p : Pattern) (selected : d368317 p = 0) : d369018 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368252 q = 0) : d368987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368252, d368987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38732 q selected
    | true =>
      simp only [d368252, d368987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38734 q selected
  have h2 (q : Pattern) (selected : d368291 q = 0) : d368992 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368291, d368992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38740 q selected
    | true =>
      simp only [d368291, d368992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38741 q selected
  have h3 (q : Pattern) (selected : d368292 q = 0) : d368993 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368292, d368993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368292, d368993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368312 q = 0) : d369013 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368312, d369013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38745 q selected
    | true =>
      simp only [d368312, d369013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368313 q = 0) : d369014 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368313, d369014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368313, d369014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368314 q = 0) : d369015 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368314, d369015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368314, d369015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368315 q = 0) : d369016 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368315, d369016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368315, d369016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368316 q = 0) : d369017 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368316, d369017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368316, d369017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d368317 q = 0) : d369018 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368317, d369018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368317, d369018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38747 (p : Pattern) (selected : d368322 p = 0) : d368991 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368246 q = 0) : d368981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368246, d368981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38733 q selected
    | true =>
      simp only [d368246, d368981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368247 q = 0) : d368982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368247, d368982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368247, d368982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368319 q = 0) : d368988 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368319, d368988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368319, d368988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368320 q = 0) : d368989 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368320, d368989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368320, d368989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368321 q = 0) : d368990 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368321, d368990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368321, d368990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368322 q = 0) : d368991 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368322, d368991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368322, d368991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38748 (p : Pattern) (selected : d368328 p = 0) : d369025 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368323 q = 0) : d369020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368323, d369020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38747 q selected
    | true =>
      simp only [d368323, d369020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368324 q = 0) : d369021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368324, d369021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368324, d369021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368325 q = 0) : d369022 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368325, d369022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368325, d369022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368326 q = 0) : d369023 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368326, d369023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368326, d369023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368327 q = 0) : d369024 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368327, d369024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368327, d369024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368328 q = 0) : d369025 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368328, d369025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368328, d369025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38749 (p : Pattern) (selected : d368334 p = 0) : d369031 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368037 q = 0) : d368821 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368037, d368821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368037, d368821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38686 q selected
  have h2 (q : Pattern) (selected : d368038 q = 0) : d368822 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368038, d368822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368038, d368822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368047 q = 0) : d368831 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368047, d368831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38686 q selected
    | true =>
      simp only [d368047, d368831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38689 q selected
  have h4 (q : Pattern) (selected : d368048 q = 0) : d368832 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368048, d368832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368048, d368832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368049 q = 0) : d368833 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d368049, d368833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368049, d368833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368178 q = 0) : d368913 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368178, d368913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38712 q selected
    | true =>
      simp only [d368178, d368913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38721 q selected
  have h7 (q : Pattern) (selected : d368191 q = 0) : d368926 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368191, d368926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38722 q selected
    | true =>
      simp only [d368191, d368926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38723 q selected
  have h8 (q : Pattern) (selected : d368192 q = 0) : d368927 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368192, d368927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368192, d368927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d368193 q = 0) : d368928 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d368193, d368928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368193, d368928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d368194 q = 0) : d368929 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d368194, d368929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368194, d368929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368198 q = 0) : d368933 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368198, d368933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368198, d368933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38724 q selected
  have h12 (q : Pattern) (selected : d368200 q = 0) : d368935 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368200, d368935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368200, d368935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38725 q selected
  have h13 (q : Pattern) (selected : d368201 q = 0) : d368936 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368201, d368936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d368201, d368936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d368202 q = 0) : d368937 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d368202, d368937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d368202, d368937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d368203 q = 0) : d368938 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d368203, d368938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d368203, d368938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d368204 q = 0) : d368939 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d368204, d368939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368204, d368939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d368318 q = 0) : d369019 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368318, d369019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368318, d369019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38746 q selected
  have h18 (q : Pattern) (selected : d368329 q = 0) : d369026 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368329, d369026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368329, d369026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38748 q selected
  have h19 (q : Pattern) (selected : d368330 q = 0) : d369027 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368330, d369027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d368330, d369027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d368331 q = 0) : d369028 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d368331, d369028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d368331, d369028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d368332 q = 0) : d369029 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d368332, d369029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d368332, d369029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d368333 q = 0) : d369030 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d368333, d369030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d368333, d369030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d368334 q = 0) : d369031 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d368334, d369031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d368334, d369031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
end NetHack.Soko22Hazard87
